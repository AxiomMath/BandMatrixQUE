module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# A measurable projection onto the kernel of a matrix

For `G : Matrix m c ℂ` let `A = GᴴG = U diag(λ) Uᴴ` (spectral theorem, `λ ≥ 0`). The spectral
projection `specProj G = U diag(1{λ = 0}) Uᴴ` is the limit of the Tikhonov resolvents
`ε (A + ε)⁻¹ = U diag(ε/(λ+ε)) Uᴴ` (`tendsto_resolv`), hence a measurable function of `G`
(`measurable_specProj`). `mul_specProj`: `G Π = 0`; `specProj_mulVec_of`: `G a = 0 ⇒ Π a = a`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open Matrix Filter Topology MeasureTheory
open scoped ComplexOrder

variable {m c : Type*} [Fintype m] [Fintype c] [DecidableEq c]

/-- The spectral projection onto `ker G`. -/
def specProj (G : Matrix m c ℂ) : Matrix c c ℂ :=
  ((isHermitian_conjTranspose_mul_self G).eigenvectorUnitary : Matrix c c ℂ) *
    diagonal (fun i => if (isHermitian_conjTranspose_mul_self G).eigenvalues i = 0 then 1 else 0) *
    star ((isHermitian_conjTranspose_mul_self G).eigenvectorUnitary : Matrix c c ℂ)

/-- The Tikhonov resolvent `ε (GᴴG + ε)⁻¹`. -/
def resolv (G : Matrix m c ℂ) (ε : ℝ) : Matrix c c ℂ :=
  (ε : ℂ) • (Gᴴ * G + (ε : ℂ) • 1)⁻¹

theorem resolv_eq (G : Matrix m c ℂ) {ε : ℝ} (hε : 0 < ε) :
    resolv G ε = ((isHermitian_conjTranspose_mul_self G).eigenvectorUnitary : Matrix c c ℂ) *
      diagonal (fun i => ((ε / ((isHermitian_conjTranspose_mul_self G).eigenvalues i + ε) : ℝ) : ℂ)) *
      star ((isHermitian_conjTranspose_mul_self G).eigenvectorUnitary : Matrix c c ℂ) := by
  set hA := isHermitian_conjTranspose_mul_self G
  set U : Matrix c c ℂ := (hA.eigenvectorUnitary : Matrix c c ℂ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hlam0 : ∀ i, 0 ≤ hA.eigenvalues i :=
    (posSemidef_conjTranspose_mul_self G).eigenvalues_nonneg
  have hspec : Gᴴ * G = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  set d : c → ℂ := fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ)
  have hd : ∀ i, d i ≠ 0 := fun i => by
    simp only [d, ne_eq, Complex.ofReal_eq_zero]; linarith [hlam0 i]
  have hsum : Gᴴ * G + (ε : ℂ) • 1 = U * diagonal d * star U := by
    rw [hspec]
    have : (ε : ℂ) • (1 : Matrix c c ℂ) = U * diagonal (fun _ => (ε : ℂ)) * star U := by
      rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU2]
    rw [this, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
    congr 3
    funext i; simp [d]
  have hinv : (U * diagonal d * star U)⁻¹ = U * diagonal (fun i => (d i)⁻¹) * star U := by
    refine Matrix.inv_eq_left_inv ?_
    calc U * diagonal (fun i => (d i)⁻¹) * star U * (U * diagonal d * star U)
        = U * (diagonal (fun i => (d i)⁻¹) * (star U * U) * diagonal d) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU1, Matrix.mul_one, diagonal_mul_diagonal]
          rw [show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : ℂ) from funext fun i => inv_mul_cancel₀ (hd i),
            diagonal_one, Matrix.mul_one, hU2]
  have hD : diagonal (fun i => ((ε / (hA.eigenvalues i + ε) : ℝ) : ℂ)) =
      (ε : ℂ) • diagonal (fun i => (d i)⁻¹) := by
    rw [← diagonal_smul]
    congr 1
    funext i
    simp [d, div_eq_mul_inv]
  rw [resolv, hsum, hinv, hD, Matrix.mul_smul, Matrix.smul_mul]

theorem tendsto_resolv (G : Matrix m c ℂ) :
    Tendsto (fun k : ℕ => resolv G (1 / ((k : ℝ) + 1))) atTop (𝓝 (specProj G)) := by
  set hA := isHermitian_conjTranspose_mul_self G
  have hlam0 : ∀ i, 0 ≤ hA.eigenvalues i :=
    (posSemidef_conjTranspose_mul_self G).eigenvalues_nonneg
  have hε : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpi : Tendsto (fun k : ℕ => fun i => ((1 / ((k : ℝ) + 1) /
      (hA.eigenvalues i + 1 / ((k : ℝ) + 1)) : ℝ) : ℂ)) atTop
      (𝓝 fun i => if hA.eigenvalues i = 0 then (1 : ℂ) else 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    by_cases h0 : hA.eigenvalues i = 0
    · simp only [h0, zero_add, ↓reduceIte]
      refine tendsto_const_nhds.congr fun k => ?_
      rw [div_self (by positivity)]; simp
    · simp only [h0, ↓reduceIte]
      have : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) / (hA.eigenvalues i + 1 / ((k : ℝ) + 1))))
          atTop (𝓝 (0 / (hA.eigenvalues i + 0))) := hε.div (tendsto_const_nhds.add hε) (by simpa)
      rw [zero_div] at this
      exact (Complex.continuous_ofReal.tendsto 0).comp this |>.congr' (Eventually.of_forall
        fun k => rfl) |>.trans (by simp)
  have hmain := ((tendsto_const_nhds (x := (hA.eigenvectorUnitary : Matrix c c ℂ))).mul
    ((continuous_id.matrix_diagonal.tendsto _).comp hpi)).mul
    (tendsto_const_nhds (x := star (hA.eigenvectorUnitary : Matrix c c ℂ)))
  refine hmain.congr fun k => ?_
  rw [resolv_eq G (by positivity)]
  rfl

theorem measurable_resolv (ε : ℝ) : Measurable fun G : Matrix m c ℂ => resolv G ε := by
  have e : (fun G : Matrix m c ℂ => resolv G ε) = fun G =>
      (ε : ℂ) • ((Gᴴ * G + (ε : ℂ) • 1).det⁻¹ • (Gᴴ * G + (ε : ℂ) • 1).adjugate) := by
    funext G
    rw [resolv, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have hc : Continuous fun G : Matrix m c ℂ => Gᴴ * G + (ε : ℂ) • 1 :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).add continuous_const
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul (hc.matrix_det.measurable.inv.mul
    (hc.matrix_adjugate.matrix_elem i j).measurable)

theorem measurable_specProj : Measurable (specProj : Matrix m c ℂ → Matrix c c ℂ) := by
  have : TopologicalSpace.PseudoMetrizableSpace (Matrix c c ℂ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c → c → ℂ))
  exact measurable_of_tendsto_metrizable (fun k => measurable_resolv _)
    (tendsto_pi_nhds.2 fun G => tendsto_resolv G)

theorem mul_specProj (G : Matrix m c ℂ) : G * specProj G = 0 := by
  set hA := isHermitian_conjTranspose_mul_self G
  set U : Matrix c c ℂ := (hA.eigenvectorUnitary : Matrix c c ℂ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hspec : Gᴴ * G = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hAP : Gᴴ * G * specProj G = 0 := by
    rw [hspec, specProj]
    change U * _ * star U * (U * _ * star U) = 0
    rw [show U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U *
        (U * diagonal (fun i => if hA.eigenvalues i = 0 then (1 : ℂ) else 0) * star U) =
        U * (diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * (star U * U) *
          diagonal (fun i => if hA.eigenvalues i = 0 then (1 : ℂ) else 0)) * star U by
        simp only [Matrix.mul_assoc], hU1, Matrix.mul_one, diagonal_mul_diagonal]
    rw [show (fun i => ((hA.eigenvalues i : ℝ) : ℂ) * if hA.eigenvalues i = 0 then (1 : ℂ) else 0) =
        fun _ => 0 from funext fun i => by by_cases h : hA.eigenvalues i = 0 <;> simp [h],
      diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]
  have : (G * specProj G)ᴴ * (G * specProj G) = 0 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Gᴴ, hAP, Matrix.mul_zero]
  exact conjTranspose_mul_self_eq_zero.1 this

theorem specProj_mulVec_of (G : Matrix m c ℂ) {a : c → ℂ} (ha : G *ᵥ a = 0) :
    specProj G *ᵥ a = a := by
  set hA := isHermitian_conjTranspose_mul_self G
  set U : Matrix c c ℂ := (hA.eigenvectorUnitary : Matrix c c ℂ)
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : Gᴴ * G = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hAa : (Gᴴ * G) *ᵥ a = 0 := by rw [← mulVec_mulVec, ha, mulVec_zero]
  have hD : diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *ᵥ (star U *ᵥ a) = 0 := by
    have h1 : star U *ᵥ ((Gᴴ * G) *ᵥ a) = 0 := by rw [hAa, mulVec_zero]
    rw [hspec, mulVec_mulVec] at h1
    rw [mulVec_mulVec, ← h1]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hE : diagonal (fun i => if hA.eigenvalues i = 0 then (1 : ℂ) else 0) *ᵥ (star U *ᵥ a) =
      star U *ᵥ a := by
    funext i
    have hi := congrFun hD i
    simp only [mulVec_diagonal, Pi.zero_apply] at hi ⊢
    by_cases h : hA.eigenvalues i = 0
    · simp [h]
    · have : (star U *ᵥ a) i = 0 := by
        rcases mul_eq_zero.1 hi with h' | h'
        · exact absurd (Complex.ofReal_eq_zero.1 h') h
        · exact h'
      simp [h, this]
  rw [specProj, ← mulVec_mulVec, ← mulVec_mulVec]
  change U *ᵥ (diagonal _ *ᵥ (star U *ᵥ a)) = a
  rw [hE, mulVec_mulVec, hU2, one_mulVec]

end BlockBand.SourceProcess.ModelExist
