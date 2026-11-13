module

public import BlockBand.Native.Johansson.Defs
public import BlockBand.DeterminantScore.WeylIntegrationInterlace

/-!
# Johansson (2.18), C2: the exponential box determinant

For `c : Fin (n+1) → ℝ` with `c_last = 0`, `c_j ≠ 0` (`j < n`), and monotone `λ : Fin (n+1) → ℝ`,

`∫_{∏(λ_i, λ_{i+1})} det[e^{μ_i c_j}]_{i,j<n} dμ = (−1)^n (∏_{j<n} c_j)^{-1} det[e^{λ_i c_j}]`

(`integral_interlaceBox_expDet`, Lebesgue measure on `ℝ^n`). Proof: multilinearity in rows
gives `det[(e^{λ_{i+1}c_j} − e^{λ_i c_j})/c_j]`; successive row differences of `det[e^{λ_i c_j}]`
make the last column `(1, 0, …, 0)`, and the expansion along the last column carries the sign
`(−1)^n` (`det_expDiffMatrix`).

Application (`orderedProfile_succ_eq`), with `c_j = (d_j − d_n)/S` and
`Δ(d) = Δ(d') ∏_{j<n}(d_n − d_j)` (`vandermonde_succ`): for `StrictMono d`, `d' = d ∘ castSucc`,
`S > 0` and `λ` in the open chamber,

`S^n Φ_{n+1}(λ) = Δ(λ) e^{−Σλ²/2S + d_nΣλ/S} ∫_{box λ} Φ_n(μ)/Δ(μ) e^{Σμ²/2S − d_nΣμ/S} dμ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory
open BlockBand.DeterminantScore.SpectralConvexity (vandermonde weylChamber)
open BlockBand.DeterminantScore.WeylIntegration (interlaceBox measurableSet_interlaceBox
  det_eq_sum_rows strictMono_of_mem_interlaceBox shiftDown shiftDown_mul_zero shiftDown_mul_succ
  det_one_sub_shiftDown)
open scoped NNReal

variable {n : ℕ}

/-!
## The box integral
-/

theorem integral_Ioo_exp_mul {a b c : ℝ} (hab : a ≤ b) (hc : c ≠ 0) :
    ∫ t in Set.Ioo a b, Real.exp (t * c) = (Real.exp (b * c) - Real.exp (a * c)) / c := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  have D : ∀ x : ℝ, HasDerivAt (fun y => Real.exp (y * c) / c) (Real.exp (x * c)) x := by
    intro x
    have := ((Real.hasDerivAt_exp (x * c)).comp x ((hasDerivAt_id x).mul_const c)).div_const c
    simp only [Function.comp_def, id] at this
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun x => (D x).deriv)
    (fun x _ => (D x).differentiableAt) (by fun_prop)]
  ring

/-- `det B = (−1)^n det[e^{λ_i c_j}]` for `B_{ij} = e^{λ_{i+1} c_j} − e^{λ_i c_j}` (`i, j < n`)
when `c_last = 0`: subtract consecutive rows and expand
along the last column (the column of ones is last, hence the sign). -/
theorem det_expDiffMatrix (c : Fin (n + 1) → ℝ) (hc : c (Fin.last n) = 0)
    (lam : Fin (n + 1) → ℝ) :
    (Matrix.of fun i j : Fin n =>
      Real.exp (lam i.succ * c j.castSucc) - Real.exp (lam i.castSucc * c j.castSucc)).det =
      (-1) ^ n * (Matrix.of fun i j => Real.exp (lam i * c j)).det := by
  set E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => Real.exp (lam i * c j)
  have h1 : ((1 - shiftDown n) * E).det = E.det := by
    rw [Matrix.det_mul, det_one_sub_shiftDown, one_mul]
  rw [← h1, Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_succ]
  have hz : ∀ i : Fin n, ((1 - shiftDown n) * E) i.succ (Fin.last n) = 0 := by
    intro i
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, shiftDown_mul_succ]
    simp [E, hc]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have h0 : ((1 - shiftDown n) * E) 0 (Fin.last n) = 1 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, shiftDown_mul_zero]
    simp [E, hc]
  rw [h0, Fin.succAbove_zero, Fin.succAbove_last]
  have hsub : (((1 - shiftDown n) * E).submatrix Fin.succ Fin.castSucc) = Matrix.of fun i j =>
      Real.exp (lam i.succ * c j.castSucc) - Real.exp (lam i.castSucc * c j.castSucc) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply,
      shiftDown_mul_succ, Matrix.of_apply, E]
  rw [hsub]
  simp only [Fin.val_zero, Fin.val_last, zero_add, mul_one]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **C2, the exponential box determinant.** For `c_last = 0`, `c_j ≠ 0` (`j < n`) and monotone
`λ`: `∫_{box λ} det[e^{μ_i c_j}]_{i,j<n} dμ = (−1)^n (∏_{j<n} c_j)^{-1} det[e^{λ_i c_j}]`. -/
theorem integral_interlaceBox_expDet (c : Fin (n + 1) → ℝ) (hc : c (Fin.last n) = 0)
    (hc0 : ∀ j : Fin n, c j.castSucc ≠ 0) (lam : Fin (n + 1) → ℝ) (hlam : Monotone lam) :
    ∫ μ in interlaceBox lam, (Matrix.of fun i j : Fin n => Real.exp (μ i * c j.castSucc)).det =
      (-1) ^ n * (∏ j : Fin n, c j.castSucc)⁻¹ *
        (Matrix.of fun i j => Real.exp (lam i * c j)).det := by
  have hab : ∀ i : Fin n, lam i.castSucc ≤ lam i.succ := fun i =>
    hlam (Fin.castSucc_le_succ i)
  have hint : ∀ (i : Fin n) (k : ℝ), Integrable (fun t : ℝ => Real.exp (t * k))
      (volume.restrict (Set.Ioo (lam i.castSucc) (lam i.succ))) :=
    fun i k => ((by fun_prop : Continuous fun t : ℝ => Real.exp (t * k)).integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  have key : ∫ μ in interlaceBox lam,
      (Matrix.of fun i j : Fin n => Real.exp (μ i * c j.castSucc)).det =
        (∏ j : Fin n, c j.castSucc)⁻¹ * (Matrix.of fun i j : Fin n =>
          Real.exp (lam i.succ * c j.castSucc) - Real.exp (lam i.castSucc * c j.castSucc)).det := by
    simp_rw [det_eq_sum_rows (Matrix.of _), Matrix.of_apply]
    unfold interlaceBox
    rw [volume_pi, Measure.restrict_pi_pi, integral_finsetSum]
    · simp_rw [integral_const_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => Real.exp (t * c (σ i).castSucc))]
      simp_rw [integral_Ioo_exp_mul (hab _) (hc0 _)]
      rw [mul_left_comm]
      congr 1
      rw [← Equiv.prod_comp σ (fun j => c j.castSucc), ← Finset.prod_inv_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [div_eq_inv_mul]
    · intro σ _
      exact (Integrable.fintype_prod (f := fun i (t : ℝ) => Real.exp (t * c (σ i).castSucc))
        fun i => hint i _).const_mul _
  rw [key, det_expDiffMatrix c hc]
  ring

/-!
## Application to the ordered profile
-/

/-- `Δ(d) = Δ(d') ∏_{j<n}(d_n − d_j)`, `d' = d ∘ castSucc`. -/
theorem vandermonde_succ (d : Fin (n + 1) → ℝ) :
    vandermonde d =
      vandermonde (fun j => d j.castSucc) * ∏ j : Fin n, (d (Fin.last n) - d j.castSucc) := by
  unfold vandermonde
  rw [Fin.prod_univ_castSucc]
  have hlast : (∏ j : Fin (n + 1),
      if Fin.last n < j then d j - d (Fin.last n) else 1) = 1 :=
    Finset.prod_eq_one fun j _ => by simp [not_lt.2 (Fin.le_last j)]
  rw [hlast, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp [Fin.castSucc_lt_last]

/-- Shifting the sources: `det[e^{μ_i (d_j − e)/S}] = E(μ, d/S) e^{−e Σμ/S}`. -/
theorem det_exp_shift {m : ℕ} (S : ℝ≥0) (d : Fin m → ℝ) (e : ℝ) (μ : Fin m → ℝ) :
    (Matrix.of fun i j => Real.exp (μ i * ((d j - e) / (S : ℝ)))).det =
      expDet S d μ * Real.exp (-(e * ∑ i, μ i) / (S : ℝ)) := by
  have h : (Matrix.of fun i j => Real.exp (μ i * ((d j - e) / (S : ℝ)))) =
      Matrix.of fun i j => Real.exp (-(e * μ i) / (S : ℝ)) *
        (Matrix.of fun i j => Real.exp (μ i * d j / (S : ℝ))) i j := by
    ext i j
    simp only [Matrix.of_apply, ← Real.exp_add]
    congr 1
    ring
  rw [h, Matrix.det_mul_column, ← Real.exp_sum, expDet, mul_comm]
  congr 2
  rw [Finset.mul_sum]
  simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

theorem orderedProfile_div_vandermonde {m : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin m → ℝ) (e : ℝ)
    {μ : Fin m → ℝ} (hμ : μ ∈ weylChamber m) :
    orderedProfile S d μ / vandermonde μ *
        Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - e * (∑ i, μ i) / (S : ℝ)) =
      (Matrix.of fun i j => Real.exp (μ i * ((d j - e) / (S : ℝ)))).det / vandermonde d := by
  have hV := (BlockBand.DeterminantScore.SpectralConvexity.vandermonde_pos hμ).ne'
  have hSR : (S : ℝ) ≠ 0 := (NNReal.coe_pos.2 hS).ne'
  rw [det_exp_shift, orderedProfile, sub_eq_add_neg, Real.exp_add]
  have hE : Real.exp (-(∑ i, μ i ^ 2) / (2 * (S : ℝ))) *
      Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ))) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  have key : ∀ a b x : ℝ, a * b = 1 → vandermonde μ / vandermonde d * expDet S d μ * a /
      vandermonde μ * (b * x) = expDet S d μ * x / vandermonde d := by
    intro a b x hab
    rw [show vandermonde μ / vandermonde d * expDet S d μ * a / vandermonde μ * (b * x) =
      expDet S d μ * x / vandermonde d * (vandermonde μ / vandermonde μ) * (a * b) by ring,
      div_self hV, hab]
    ring
  rw [neg_div (S : ℝ) (e * ∑ i, μ i)]
  exact key _ _ _ hE

/-- **C2, application to the ordered profile.** For `S > 0`, `StrictMono d`, `d' = d ∘ castSucc`,
`d_n = d_last` and `λ` in the open chamber,
`S^n Φ_{n+1}(λ) = Δ(λ) e^{−Σλ²/2S + d_nΣλ/S} ∫_{box λ} Φ_n(μ)/Δ(μ) e^{Σμ²/2S − d_nΣμ/S} dμ`. -/
theorem orderedProfile_succ_eq (S : ℝ≥0) (hS : 0 < S) (d : Fin (n + 1) → ℝ) (hd : StrictMono d)
    {lam : Fin (n + 1) → ℝ} (hlam : lam ∈ weylChamber (n + 1)) :
    (S : ℝ) ^ n * orderedProfile S d lam =
      vandermonde lam * Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) +
          d (Fin.last n) * (∑ i, lam i) / (S : ℝ)) *
        ∫ μ in interlaceBox lam, orderedProfile S (fun j => d j.castSucc) μ / vandermonde μ *
          Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ)) := by
  set dn := d (Fin.last n) with hdn
  set c : Fin (n + 1) → ℝ := fun j => (d j - dn) / (S : ℝ) with hcdef
  have hSR : (0 : ℝ) < S := NNReal.coe_pos.2 hS
  have hc : c (Fin.last n) = 0 := by simp [c, dn]
  have hlt : ∀ j : Fin n, d j.castSucc < dn := fun j => hd (Fin.castSucc_lt_last j)
  have hc0 : ∀ j : Fin n, c j.castSucc ≠ 0 := fun j =>
    div_ne_zero (sub_ne_zero.2 (hlt j).ne) hSR.ne'
  have hd' : StrictMono fun j : Fin n => d j.castSucc := hd.comp Fin.strictMono_castSucc
  have hVd' := (BlockBand.DeterminantScore.SpectralConvexity.vandermonde_pos hd').ne'
  have hint : ∫ μ in interlaceBox lam, orderedProfile S (fun j => d j.castSucc) μ /
      vandermonde μ * Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - dn * (∑ i, μ i) / (S : ℝ)) =
      (∫ μ in interlaceBox lam,
        (Matrix.of fun i j : Fin n => Real.exp (μ i * c j.castSucc)).det) /
          vandermonde (fun j => d j.castSucc) := by
    rw [← integral_div]
    refine setIntegral_congr_fun (measurableSet_interlaceBox lam) fun μ hμ => ?_
    exact orderedProfile_div_vandermonde S hS _ dn
      (strictMono_of_mem_interlaceBox (show StrictMono lam from hlam).monotone hμ)
  rw [hint, integral_interlaceBox_expDet c hc hc0 lam (show StrictMono lam from hlam).monotone,
    show (Matrix.of fun i j => Real.exp (lam i * c j)) =
      Matrix.of fun i j => Real.exp (lam i * ((d j - dn) / (S : ℝ))) from rfl,
    det_exp_shift, orderedProfile, vandermonde_succ d]
  have hP : ∏ j : Fin n, c j.castSucc = (-1) ^ n * (∏ j : Fin n, (dn - d j.castSucc)) /
      (S : ℝ) ^ n := by
    simp only [c]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    calc ∏ j : Fin n, (d j.castSucc - dn) = ∏ j : Fin n, ((-1) * (dn - d j.castSucc)) :=
          Finset.prod_congr rfl fun j _ => by ring
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
  have hPne : ∏ j : Fin n, (dn - d j.castSucc) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hlt j).ne'
  rw [hP, Real.exp_add]
  have hE' : Real.exp (dn * (∑ i, lam i) / (S : ℝ)) *
      Real.exp (-(dn * (∑ i, lam i) / (S : ℝ))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  field_simp
  rw [← hdn, mul_div_assoc, div_self hPne, mul_one, mul_assoc _ (Real.exp _), hE', mul_one]

end BlockBand.Native.Johansson
