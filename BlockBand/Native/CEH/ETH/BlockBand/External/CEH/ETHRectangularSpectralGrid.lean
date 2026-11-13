module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ETHDeterministicExtraction

/-!
# Rectangular spectral grids for CEH extraction

This module removes any need for a Lipschitz estimate on the canonical typical-spacing
function in the deterministic random-point-to-grid passage.  Instead of lifting a
one-dimensional energy grid at varying heights, it covers the whole deterministic
energy-height rectangle by a product grid.  The cost is only a second finite grid
cardinality, which is harmless for polynomial meshes and preserves the exact
fixed-parameter-before-tail-exponent quantifier order.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Uniform grid on the height interval `[etaMin, etaMax]`. -/
def localETHHeightGridPoint (etaMin etaMax : ℝ) (meshCount : ℕ)
    (b : Fin (meshCount + 1)) : ℝ :=
  localETHRealGridPoint ((etaMin + etaMax) / 2) ((etaMax - etaMin) / 2)
    meshCount b

/-- Every height-grid point belongs to its closed height interval. -/
theorem localETHHeightGridPoint_mem_Icc
    {etaMin etaMax : ℝ} {meshCount : ℕ} (heta : etaMin ≤ etaMax)
    (hm : 0 < meshCount) (b : Fin (meshCount + 1)) :
    localETHHeightGridPoint etaMin etaMax meshCount b ∈
      Set.Icc etaMin etaMax := by
  have hR : 0 ≤ (etaMax - etaMin) / 2 := by linarith
  have h := localETHRealGridPoint_mem_Icc
    (E₀ := (etaMin + etaMax) / 2) hR hm b
  simpa only [localETHHeightGridPoint,
    show (etaMin + etaMax) / 2 - (etaMax - etaMin) / 2 = etaMin by ring,
    show (etaMin + etaMax) / 2 + (etaMax - etaMin) / 2 = etaMax by ring] using h

/-- Every height in a nondegenerate closed interval is within one mesh step
of the concrete height grid. -/
theorem exists_localETHHeightGridPoint_near
    {etaMin etaMax eta : ℝ} {meshCount : ℕ} (heta : etaMin < etaMax)
    (hm : 0 < meshCount) (hmem : eta ∈ Set.Icc etaMin etaMax) :
    ∃ b : Fin (meshCount + 1),
      |eta - localETHHeightGridPoint etaMin etaMax meshCount b| ≤
        (etaMax - etaMin) / meshCount := by
  have hR : 0 < (etaMax - etaMin) / 2 := by linarith
  have hmem' : eta ∈ Set.Icc
      ((etaMin + etaMax) / 2 - (etaMax - etaMin) / 2)
      ((etaMin + etaMax) / 2 + (etaMax - etaMin) / 2) := by
    simpa only [show (etaMin + etaMax) / 2 - (etaMax - etaMin) / 2 = etaMin by ring,
      show (etaMin + etaMax) / 2 + (etaMax - etaMin) / 2 = etaMax by ring] using hmem
  obtain ⟨b, hb⟩ := exists_localETHRealGridPoint_near hR hm hmem'
  refine ⟨b, ?_⟩
  simpa [localETHHeightGridPoint, show 2 * ((etaMax - etaMin) / 2) =
    etaMax - etaMin by ring] using hb

/-- Product grid on an energy-height rectangle in the upper half-plane. -/
def localETHRectangularSpectralGridPoint
    (E₀ R etaMin etaMax : ℝ) (realMesh heightMesh : ℕ)
    (ab : Fin (realMesh + 1) × Fin (heightMesh + 1)) : ℂ :=
  (localETHRealGridPoint E₀ R realMesh ab.1 : ℂ) +
    (localETHHeightGridPoint etaMin etaMax heightMesh ab.2 : ℂ) * Complex.I

/-- The product-grid cardinality is the product of the two mesh
cardinalities. -/
theorem card_localETHRectangularSpectralGridIndex
    (realMesh heightMesh : ℕ) :
    Fintype.card (Fin (realMesh + 1) × Fin (heightMesh + 1)) =
      (realMesh + 1) * (heightMesh + 1) := by
  simp

/-- Every point in the energy-height rectangle is close to a product-grid
point.  The displayed radius is the sum of the two one-dimensional mesh
steps, avoiding a square-root constant. -/
theorem exists_localETHRectangularSpectralGridPoint_near
    {E₀ R etaMin etaMax x eta : ℝ} {realMesh heightMesh : ℕ}
    (hR : 0 < R) (heta : etaMin < etaMax)
    (hrm : 0 < realMesh) (hhm : 0 < heightMesh)
    (hx : x ∈ Set.Icc (E₀ - R) (E₀ + R))
    (hheight : eta ∈ Set.Icc etaMin etaMax) :
    ∃ ab : Fin (realMesh + 1) × Fin (heightMesh + 1),
      ‖((x : ℂ) + (eta : ℂ) * Complex.I) -
          localETHRectangularSpectralGridPoint
            E₀ R etaMin etaMax realMesh heightMesh ab‖ ≤
        2 * R / realMesh + (etaMax - etaMin) / heightMesh := by
  obtain ⟨a, ha⟩ := exists_localETHRealGridPoint_near hR hrm hx
  obtain ⟨b, hb⟩ := exists_localETHHeightGridPoint_near heta hhm hheight
  refine ⟨(a, b), ?_⟩
  rw [show ((x : ℂ) + (eta : ℂ) * Complex.I) -
      localETHRectangularSpectralGridPoint
        E₀ R etaMin etaMax realMesh heightMesh (a, b) =
      ((x - localETHRealGridPoint E₀ R realMesh a : ℝ) : ℂ) +
        ((eta - localETHHeightGridPoint etaMin etaMax heightMesh b : ℝ) : ℂ) *
          Complex.I by
    simp [localETHRectangularSpectralGridPoint]
    ring]
  calc
    ‖((x - localETHRealGridPoint E₀ R realMesh a : ℝ) : ℂ) +
        ((eta - localETHHeightGridPoint etaMin etaMax heightMesh b : ℝ) : ℂ) *
          Complex.I‖ ≤
      ‖((x - localETHRealGridPoint E₀ R realMesh a : ℝ) : ℂ)‖ +
        ‖((eta - localETHHeightGridPoint etaMin etaMax heightMesh b : ℝ) : ℂ) *
          Complex.I‖ := norm_add_le _ _
    _ = |x - localETHRealGridPoint E₀ R realMesh a| +
        |eta - localETHHeightGridPoint etaMin etaMax heightMesh b| := by
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rfl
    _ ≤ 2 * R / realMesh + (etaMax - etaMin) / heightMesh := add_le_add ha hb

/-- Callback-free random CEH spectral-point passage to a two-dimensional
product grid.  Unlike the one-dimensional lifted grid, this theorem assumes
only deterministic lower and upper height bounds, not a modulus for `etaF`. -/
theorem localETHTwoResolventRandomBadEvent_subset_rectangularGrid
    {Ω : Type*} {N realMesh heightMesh : ℕ} (hN : 0 < N)
    (H : Ω → Matrix (Fin N) (Fin N) ℂ)
    (hH : ∀ ω, (H ω).IsHermitian)
    (c₁ c₂ : AdjointChoice) (A : Matrix (Fin N) (Fin N) ℂ)
    (etaF : ℝ → ℝ) (ξ E₀ R etaMin etaMax : ℝ)
    (hR : 0 < R) (hrm : 0 < realMesh) (hhm : 0 < heightMesh)
    (hetaMin : 0 < etaMin) (hetaRange : etaMin < etaMax)
    (lam : Ω → Fin N → ℝ)
    (hlam : ∀ ω i, lam ω i ∈ Set.Icc (E₀ - R) (E₀ + R))
    (hheight : ∀ ω i,
      (N : ℝ) ^ ξ * etaF (lam ω i) ∈ Set.Icc etaMin etaMax)
    (threshold : Fin N → Fin N → ℝ) (gridThreshold : ℝ)
    (hbudget : ∀ i j,
      gridThreshold +
          2 * (2 * R / realMesh + (etaMax - etaMin) / heightMesh) *
            etaMin⁻¹ ^ 3 * ‖A‖ ≤ threshold i j) :
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
        (localETHRectangularSpectralGridPoint
          E₀ R etaMin etaMax realMesh heightMesh)
        gridThreshold := by
  intro ω hω
  rcases hω with ⟨i, j, hij⟩
  let zi := CEHNative.BlockBand.localETHSpectralPoint
    N etaF ξ (lam ω i)
  let zj := CEHNative.BlockBand.localETHSpectralPoint
    N etaF ξ (lam ω j)
  obtain ⟨ai, hai⟩ := exists_localETHRectangularSpectralGridPoint_near
    hR hetaRange hrm hhm (hlam ω i) (hheight ω i)
  obtain ⟨aj, haj⟩ := exists_localETHRectangularSpectralGridPoint_near
    hR hetaRange hrm hhm (hlam ω j) (hheight ω j)
  let wi := localETHRectangularSpectralGridPoint
    E₀ R etaMin etaMax realMesh heightMesh ai
  let wj := localETHRectangularSpectralGridPoint
    E₀ R etaMin etaMax realMesh heightMesh aj
  have hzi : etaMin ≤ |zi.im| := by
    have hlo := (hheight ω i).1
    have hp : 0 < (N : ℝ) ^ ξ * etaF (lam ω i) :=
      hetaMin.trans_le hlo
    rw [show zi.im = (N : ℝ) ^ ξ * etaF (lam ω i) by
      simp [zi, CEHNative.BlockBand.localETHSpectralPoint]]
    rw [abs_of_pos hp]
    exact hlo
  have hzj : etaMin ≤ |zj.im| := by
    have hlo := (hheight ω j).1
    have hp : 0 < (N : ℝ) ^ ξ * etaF (lam ω j) :=
      hetaMin.trans_le hlo
    rw [show zj.im = (N : ℝ) ^ ξ * etaF (lam ω j) by
      simp [zj, CEHNative.BlockBand.localETHSpectralPoint]]
    rw [abs_of_pos hp]
    exact hlo
  have hwiMem := localETHHeightGridPoint_mem_Icc hetaRange.le hhm ai.2
  have hwjMem := localETHHeightGridPoint_mem_Icc hetaRange.le hhm aj.2
  have hwi : etaMin ≤ |wi.im| := by
    have hp : 0 < localETHHeightGridPoint etaMin etaMax heightMesh ai.2 :=
      hetaMin.trans_le hwiMem.1
    simpa [wi, localETHRectangularSpectralGridPoint, abs_of_pos hp] using hwiMem.1
  have hwj : etaMin ≤ |wj.im| := by
    have hp : 0 < localETHHeightGridPoint etaMin etaMax heightMesh aj.2 :=
      hetaMin.trans_le hwjMem.1
    simpa [wj, localETHRectangularSpectralGridPoint, abs_of_pos hp] using hwjMem.1
  have hmod := norm_twoResolventObservable_cehHermitianResolvent_sub_le
    hN (H ω) (hH ω) c₁ c₂ A hetaMin hzi hwi hzj hwj hai haj
  refine ⟨ai, aj, ?_⟩
  have hnorm := norm_le_norm_add_norm_sub'
    (twoResolventObservable c₁ c₂
      (cehHermitianResolvent (H ω) zi) A
      (cehHermitianResolvent (H ω) zj))
    (twoResolventObservable c₁ c₂
      (cehHermitianResolvent (H ω) wi) A
      (cehHermitianResolvent (H ω) wj))
  calc
    gridThreshold ≤ threshold i j -
        2 * (2 * R / realMesh + (etaMax - etaMin) / heightMesh) *
          etaMin⁻¹ ^ 3 * ‖A‖ := by linarith [hbudget i j]
    _ ≤ ‖twoResolventObservable c₁ c₂
          (cehHermitianResolvent (H ω) zi) A
          (cehHermitianResolvent (H ω) zj)‖ -
        2 * (2 * R / realMesh + (etaMax - etaMin) / heightMesh) *
          etaMin⁻¹ ^ 3 * ‖A‖ := by linarith
    _ ≤ ‖twoResolventObservable c₁ c₂
          (cehHermitianResolvent (H ω) wi) A
          (cehHermitianResolvent (H ω) wj)‖ := by linarith [hmod, hnorm]

end CEHNative.BlockBand.External.CEH
