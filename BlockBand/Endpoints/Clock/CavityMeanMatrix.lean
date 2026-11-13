module

public import BlockBand.Endpoints.Clock.CavityMeanStability

/-!
# Matrix form of the deterministic cavity map

For a Hermitian `W × W` matrix `X`, the normalized resolvent trace `W⁻¹ Tr (ζ - X)⁻¹` is the
Stieltjes transform of the eigenvalue law, so the cavity equations with this `f` have a unique
solution with negative imaginary parts (`cavityMatrix_existsUnique`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Complex Matrix

/-- `f(ζ) = W⁻¹ Tr (ζ - X)⁻¹`, the normalized trace of the resolvent (sign convention of
the cavity-mean lemma). -/
def normalizedResolventTrace {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) : ℂ :=
  (W : ℂ)⁻¹ * ((ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace

/-- The uniform weights `1/W` are probability weights. -/
theorem isCavityWeights_uniform {W : ℕ} (hW : 0 < W) :
    IsCavityWeights (fun _ : Fin W => (W : ℝ)⁻¹) := by
  refine ⟨fun _ => by positivity, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `W⁻¹ Tr (ζ - X)⁻¹ = Σ_j W⁻¹ (ζ - λ_j)⁻¹` for Hermitian `X` and nonreal `ζ`. -/
theorem normalizedResolventTrace_eq {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    normalizedResolventTrace X ζ = cavityStieltjes (fun _ => (W : ℝ)⁻¹) hX.eigenvalues ζ := by
  set U : Matrix (Fin W) (Fin W) ℂ := (hX.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)
  have hU1 : U * star U = 1 := Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  have hU2 : star U * U = 1 := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  set lam : Fin W → ℂ := fun i => ((hX.eigenvalues i : ℝ) : ℂ)
  have hspec : X = U * Matrix.diagonal lam * star U := by
    have h := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hne : ∀ i, ζ - lam i ≠ 0 := by
    intro i h
    have := congrArg Complex.im h
    simp [lam] at this
    exact hζ this
  have hshift : ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X =
      U * Matrix.diagonal (fun i => ζ - lam i) * star U := by
    have : Matrix.diagonal (fun i => ζ - lam i) = ζ • 1 - Matrix.diagonal lam := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hspec, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hU1]
  have hinv : (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ =
      U * Matrix.diagonal (fun i => (ζ - lam i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hshift]
    calc U * Matrix.diagonal (fun i => ζ - lam i) * star U *
          (U * Matrix.diagonal (fun i => (ζ - lam i)⁻¹) * star U)
        = U * (Matrix.diagonal (fun i => ζ - lam i) * (star U * U) *
            Matrix.diagonal (fun i => (ζ - lam i)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU2, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          have : (fun i => (ζ - lam i) * (ζ - lam i)⁻¹) = fun _ => (1 : ℂ) := by
            funext i
            exact mul_inv_cancel₀ (hne i)
          rw [this, Matrix.diagonal_one, Matrix.mul_one, hU1]
  unfold normalizedResolventTrace cavityStieltjes
  rw [hinv, Matrix.trace_mul_cycle, hU2, Matrix.one_mul, Matrix.trace_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [lam]

/-- `(v, u)` solves the cavity equations for the matrix `X`, with negative imaginary parts. -/
def IsCavityMatrixSolution {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (b c e : ℝ) (z' v u : ℂ) :
    Prop :=
  v = normalizedResolventTrace X (-e - c * v - b * u) ∧ u = (z' - b * v)⁻¹ ∧ v.im < 0 ∧ u.im < 0

theorem isCavityMatrixSolution_iff {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    {b c e : ℝ} (hb : 0 < b) (hc : 0 < c) {z' v u : ℂ} :
    IsCavityMatrixSolution X b c e z' v u ↔
      IsCavitySolution (fun _ => (W : ℝ)⁻¹) hX.eigenvalues b c e z' v u := by
  have key : v.im < 0 → u.im < 0 → (-(e : ℂ) - c * v - b * u).im ≠ 0 := by
    intro hv hu
    have : (-(e : ℂ) - c * v - b * u).im = c * (-v.im) + b * (-u.im) := by simp; ring
    rw [this]
    have := mul_pos hc (neg_pos.mpr hv); have := mul_pos hb (neg_pos.mpr hu)
    exact ne_of_gt (by linarith)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by rw [← normalizedResolventTrace_eq hX (key h3 h4)]; exact h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by rw [normalizedResolventTrace_eq hX (key h3 h4)]; exact h1, h2, h3, h4⟩

/-- **the cavity-mean lemma, first sentence**: for an `W × W` Hermitian `X`
(`W ≥ 1`), `b, c > 0` and `Im z' > 0`, the equations the cavity equations with
`f(ζ) = W⁻¹ Tr(ζ - X)⁻¹` have a unique solution with negative imaginary parts. -/
theorem cavityMatrix_existsUnique {W : ℕ} (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) {b c e : ℝ} (hb : 0 < b) (hc : 0 < c) {z' : ℂ} (hz : 0 < z'.im) :
    ∃ vu : ℂ × ℂ, IsCavityMatrixSolution X b c e z' vu.1 vu.2 ∧
      ∀ v u : ℂ, IsCavityMatrixSolution X b c e z' v u → v = vu.1 ∧ u = vu.2 := by
  obtain ⟨vu, h, huniq⟩ := cavity_existsUnique (x := hX.eigenvalues) (e := e)
    (isCavityWeights_uniform hW) hb hc hz
  refine ⟨vu, (isCavityMatrixSolution_iff hX hb hc).mpr h, fun v u h' => huniq v u ?_⟩
  exact (isCavityMatrixSolution_iff hX hb hc).mp h'

end BlockBand.Endpoints.Clock
