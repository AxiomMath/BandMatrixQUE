module

public import BlockBand.Transmission.PassiveLayer.BilFixed
public import BlockBand.Transmission.PassiveLayer.BilFatou

/-!
# Auxiliary lemmas for the `bilinear` clause

* `norm_cZero_le`: `|c₀| = 1/(2η) ≤ 1/((1-b)κ)` on `bulkInterval κ`.
* `weight_moms`: `L^p` bounds of `(k+l)²g(g+γ)` and `(k+l)²(g+γ)` from `L^{8p}` bounds.
* `bilinear_sub_matrixExpect`: `u*(U - EU)v = u*Uv - E[u*Uv]` (entrywise integrable `U`).
* `tendsto_psiLayer_reg`: the functional at `X - iε_n`, `ε_n = 1/(n+1)`, converges to the one at
  `X` wherever the layer matrix at `X` is invertible.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal

open BlockBand.Transmission

variable {W : ℕ}

theorem norm_cZero_le {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖cZero b E‖ ≤ 1 / ((1 - b) * κ) := by
  obtain ⟨hE1, hE2⟩ := hE
  have hη : etaZ b E = (1 - b) * Real.sqrt (4 - E ^ 2) / 2 :=
    Bridge.boundaryZ_im b E (by nlinarith)
  have hs : κ ≤ Real.sqrt (4 - E ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h1b : 0 < 1 - b := by linarith
  have hηl : (1 - b) * κ / 2 ≤ etaZ b E := by rw [hη]; nlinarith
  have hηp : 0 < etaZ b E := lt_of_lt_of_le (by positivity) hηl
  rw [cZero, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_of_nonneg hηp.le]
  rw [show ‖(2 : ℂ)‖ = 2 by simp, inv_eq_one_div]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  linarith

/-- Moments of the gradient weight and of the functional's dominating polynomial. -/
theorem weight_moms {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g k l : Ω → ℝ} {p Cm γ : ℝ} (hp : 1 ≤ p) (hCm : 0 ≤ Cm) (hγ : 0 ≤ γ)
    (hg : MomBd μ g (8 * p) Cm) (hk : MomBd μ k (8 * p) Cm) (hl : MomBd μ l (8 * p) Cm) :
    MomBd μ (fun x => ((k x + l x) * (k x + l x)) * (g x * (g x + γ))) p
        ((2 * Cm) * (2 * Cm) * (Cm * (Cm + γ))) ∧
      MomBd μ (fun x => ((k x + l x) * (k x + l x)) * (g x + γ)) p
        ((2 * Cm) * (2 * Cm) * (Cm + γ)) := by
  have hp0 : 0 < p := by linarith
  have e4 : ∀ {f : Ω → ℝ}, MomBd μ f (8 * p) Cm → MomBd μ f (2 * (2 * p)) Cm :=
    fun h => h.exponent_mono (by linarith)
  have hkl : MomBd μ (fun x => k x + l x) (2 * (2 * p)) (Cm + Cm) :=
    (e4 hk).add (by linarith) (e4 hl) hCm hCm
  have hkl2 : MomBd μ (fun x => (k x + l x) * (k x + l x)) (2 * p) ((Cm + Cm) * (Cm + Cm)) :=
    MomBd.mul (by positivity) hkl hkl (by positivity)
  have hγc : MomBd μ (fun _ => γ) (2 * (2 * p)) γ := by
    simpa [abs_of_nonneg hγ] using MomBd.const (μ := μ) γ (2 * (2 * p)) (by positivity)
  have hgγ : MomBd μ (fun x => g x + γ) (2 * (2 * p)) (Cm + γ) :=
    (e4 hg).add (by linarith) hγc hCm hγ
  have hggγ : MomBd μ (fun x => g x * (g x + γ)) (2 * p) (Cm * (Cm + γ)) :=
    MomBd.mul (by positivity) (e4 hg) hgγ hCm
  have e2 : (Cm + Cm) = 2 * Cm := by ring
  refine ⟨?_, ?_⟩
  · have := MomBd.mul hp0 hkl2 hggγ (by positivity)
    rwa [e2] at this
  · have := MomBd.mul hp0 hkl2 (hgγ.exponent_mono (by linarith)) (by positivity)
    rwa [e2] at this

/-- `u*(U - EU)v = u*Uv - E[u*Uv]` for an entrywise integrable random matrix. -/
theorem bilinear_sub_matrixExpect {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    {μ : Measure Ω} (U : Ω → Matrix n n ℂ) (hU : ∀ x y, Integrable (fun ω => U ω x y) μ)
    (u v : n → ℂ) (ω : Ω) :
    bilinear u (U ω - matrixExpect μ U) v =
      bilinear u (U ω) v - ∫ ω', bilinear u (U ω') v ∂μ := by
  have h : ∫ ω', bilinear u (U ω') v ∂μ = bilinear u (matrixExpect μ U) v := by
    simp only [bilinear, dotProduct, mulVec, Pi.star_apply, matrixExpect, Matrix.of_apply]
    rw [integral_finsetSum _ fun x _ => ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_const_mul, integral_finsetSum _ fun y _ => (hU x y).mul_const _]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [integral_mul_const]
    · exact (integrable_finsetSum _ fun y _ => (hU x y).mul_const _).const_mul _
  rw [h, bilinear, bilinear, bilinear, sub_mulVec, dotProduct_sub]

theorem bilinear_single (M : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W) :
    bilinear (Pi.single x 1) M (Pi.single y 1) = M x y := by
  simp [bilinear, dotProduct, mulVec, Pi.single_apply]

theorem vecNorm_single (x : Fin W) : vecNorm (Pi.single x (1 : ℂ)) = 1 := by
  simp only [vecNorm, Pi.single_apply]
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
  simp

theorem layerMatrix_regX (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)
    (ω : LayerSample W .oneBlockOnePort) :
    layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) ω =
      layerMatrix .oneBlockOnePort E w (liftX X) ω +
        ((ε : ℂ) * Complex.I) • fromBlocks (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) 0 0 0 := by
  ext i j
  rcases i with ⟨i1, i⟩ | ⟨i1, i⟩ <;> rcases j with ⟨j1, j⟩ | ⟨j1, j⟩ <;>
    obtain rfl : i1 = j1 := Subsingleton.elim _ _ <;>
    simp [layerMatrix, regX, liftX, fromBlocks, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> ring

theorem pK_regX (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) :
    pK w (regX X ε) = pK w X + ((ε : ℂ) * Complex.I) • iota1 W := by
  rw [pK, pK, regX, show w • (1 : Matrix (Fin W) (Fin W) ℂ) - (X - ((ε : ℂ) * Complex.I) • 1) =
    (w • 1 - X) + ((ε : ℂ) * Complex.I) • 1 by abel, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]

/-- The regularization sequence `ε_n = 1/(n+1)`. -/
def epsN (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem epsN_pos (n : ℕ) : 0 < epsN n := by unfold epsN; positivity

theorem tendsto_epsN_I : Tendsto (fun n : ℕ => (epsN n : ℂ) * Complex.I) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (epsN n : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [epsN, Function.comp_def] using this
  simpa using h.mul_const Complex.I

theorem tendsto_layerAt_reg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    Tendsto (fun n : ℕ => layerAt E w (regX X (epsN n)) ω) atTop (𝓝 (layerAt E w X ω)) := by
  set M := layerMatrix .oneBlockOnePort E w (liftX X) ω
  set N : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
    fromBlocks (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) 0 0 0
  have hM : Tendsto (fun n : ℕ => M + ((epsN n : ℂ) * Complex.I) • N) atTop (𝓝 M) := by
    have := (tendsto_const_nhds (x := M)).add (tendsto_epsN_I.smul_const N)
    simpa using this
  have hc : ContinuousAt (fun G : Matrix (LayerSite W .oneBlockOnePort)
      (LayerSite W .oneBlockOnePort) ℂ => G⁻¹) M := by
    have h := NormedRing.inverse_continuousAt hu.unit
    have he : (fun G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ =>
        G⁻¹) = Ring.inverse := by funext G; exact Matrix.nonsing_inv_eq_ringInverse G
    rw [he]; exact h
  have h2 := hc.tendsto.comp hM
  have e : (fun n : ℕ => layerAt E w (regX X (epsN n)) ω) =
      (fun G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ => G⁻¹) ∘
        fun n : ℕ => M + ((epsN n : ℂ) * Complex.I) • N := by
    funext n; simp only [Function.comp_apply, layerAt, layerResolvent, layerMatrix_regX, M, N]
  rw [e]; exact h2

theorem tendsto_pK_reg (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Tendsto (fun n : ℕ => pK w (regX X (epsN n))) atTop (𝓝 (pK w X)) := by
  have := (tendsto_const_nhds (x := pK w X)).add (tendsto_epsN_I.smul_const (iota1 W))
  simp only [zero_smul, add_zero] at this
  simpa only [pK_regX] using this

theorem tendsto_psiLayer_reg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω))
    (u v : Fin W → ℂ) (θ : ℂ)
    (Γ : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    Tendsto (fun n : ℕ => psiLayer E w (regX X (epsN n)) u v θ Γ ω) atTop
      (𝓝 (psiLayer E w X u v θ Γ ω)) := by
  have hvec : ∀ z : Fin W → ℂ, Tendsto (fun n : ℕ => (pK w (regX X (epsN n)))ᴴ *ᵥ z)
      atTop (𝓝 ((pK w X)ᴴ *ᵥ z)) := fun z =>
    ((continuous_id.matrix_conjTranspose.matrix_mulVec continuous_const).tendsto _).comp
      (tendsto_pK_reg w X)
  have h := ((continuous_psiMap θ (pTwo W) Γ).tendsto
    ((pK w X)ᴴ *ᵥ u, (pK w X)ᴴ *ᵥ v, layerAt E w X ω)).comp
    ((hvec u).prodMk_nhds ((hvec v).prodMk_nhds (tendsto_layerAt_reg E w X ω hu)))
  unfold psiLayer
  exact h

end BlockBand.Transmission.PassiveLayer
