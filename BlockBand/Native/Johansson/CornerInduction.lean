module

public import BlockBand.Native.Johansson.ExpBoxDet
public import BlockBand.DeterminantScore.BorderLaw
public import BlockBand.DeterminantScore.EigenDensityWeyl

/-!
# Johansson (2.18), C1 and C3: the corner induction with a source

* `profileNonneg_holds : ProfileNonnegStatement`: `Φ_N ≥ 0` on the open chamber, by induction on
  `N` from the application form of the exponential box determinant (`orderedProfile_succ_eq`).
* `sourceEigenLaw`: for `S > 0` and `StrictMono d`, there is `c > 0` such that for every measurable
  `g ≥ 0`, with `w_d(H) = exp((−Re tr H² + 2 Re tr(H D))/(2S))`, `D = diag(d)`,
  `∫ g(λ(H(y))) w_d(H(y)) dy = c ∫_𝒞 g(λ) Φ_n(λ) dλ` (Lebesgue measure on `HermCoord n`).
  Induction on the corner: `cornerFubini`, the bordered law
  `borderEigenLaw_of_diagonal complexUnitaryInvariance diagonalBorderLaw_holds` applied to
  `λ ↦ g(λ) β(λ, μ)`, the trace identities `tr B = Σλ`, `tr B² = Σλ²`
  (`sourceWeight_borderHerm`), the a.e. chamber property from the induction hypothesis
  (`ae_mem_weylChamber_of_law`), a general-weight Tonelli swap over `{λ ≻ μ}`
  (`lintegral_interlace_swap_general`) and `orderedProfile_succ_eq`.
* `orderedLaw_of_bridge : CoordinateBridgeStatement → OrderedLawStatement`: translation by `D`
  (`EigenDensity.lintegral_orderedEigs_eq`) and `Re tr(H−D)² = Re tr H² − 2 Re tr(HD) + Σd²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory
open BlockBand.DeterminantScore.Sector (HermCoord hermOfCoord isHermitian_hermOfCoord
  continuous_hermOfCoord)
open BlockBand.Internal.Contracts.CoareaPalm (freshEigenvalue)
open BlockBand.DeterminantScore.WeylIntegration (borderHerm interlaceSet interlaceAverage
  interlacePairs measurableSet_interlacePairs interlaceBox measurableSet_interlaceBox
  strictMono_lam_of_interlace strictMono_of_interlace interlaceBox_eq_empty
  strictMono_of_mem_interlaceBox cornerFubini conjDiag exists_conjDiag_freshEigenvalue
  measurable_freshEigs_hermOfCoord BorderEigenLawStatement borderEigenLaw_of_diagonal
  complexUnitaryInvariance diagonalBorderLaw_holds isHermitian_borderHerm continuous_vandermonde)
open BlockBand.DeterminantScore.SpectralConvexity (vandermonde weylChamber vandermonde_pos
  isOpen_weylChamber)
open scoped ENNReal NNReal

variable {n : ℕ}

/-!
## Positivity of the profile
-/

theorem orderedProfile_zero (S : ℝ≥0) (d lam : Fin 0 → ℝ) : orderedProfile S d lam = 1 := by
  simp [orderedProfile, expDet, vandermonde]

/-- **C2, positivity of the profile**: `Φ_N ≥ 0` on the open chamber. -/
theorem profileNonneg_holds : ProfileNonnegStatement := by
  intro N S hS
  induction N with
  | zero =>
    intro d _ lam _
    rw [orderedProfile_zero]
    exact zero_le_one
  | succ n ih =>
    intro d hd lam hlam
    have hd' : StrictMono fun j : Fin n => d j.castSucc := hd.comp Fin.strictMono_castSucc
    have hint : 0 ≤ ∫ μ in interlaceBox lam, orderedProfile S (fun j => d j.castSucc) μ /
        vandermonde μ * Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) -
          d (Fin.last n) * (∑ i, μ i) / (S : ℝ)) := by
      refine setIntegral_nonneg (measurableSet_interlaceBox lam) fun μ hμ => ?_
      have hμ' : μ ∈ weylChamber n :=
        strictMono_of_mem_interlaceBox (show StrictMono lam from hlam).monotone hμ
      exact mul_nonneg (div_nonneg (ih _ hd' μ hμ') (vandermonde_pos hμ').le)
        (Real.exp_pos _).le
    have h := orderedProfile_succ_eq S hS d hd hlam
    have h0 : 0 ≤ (S : ℝ) ^ n * orderedProfile S d lam := by
      rw [h]
      exact mul_nonneg (mul_nonneg (vandermonde_pos hlam).le (Real.exp_pos _).le) hint
    exact (mul_nonneg_iff_of_pos_left (pow_pos (NNReal.coe_pos.2 hS) n)).1 h0

/-!
## Trace identities
-/

theorem trace_re_eq_sum_freshEigenvalue {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) : H.trace.re = ∑ k, freshEigenvalue H k := by
  obtain ⟨W, hW⟩ := exists_conjDiag_freshEigenvalue hH
  set lam := fun k => freshEigenvalue H k
  have hWW : star (W : Matrix (Fin m) (Fin m) ℂ) * (W : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self W
  rw [hW, conjDiag, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWW, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem trace_sq_re_eq_sum_freshEigenvalue {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) : (H * H).trace.re = ∑ k, freshEigenvalue H k ^ 2 := by
  obtain ⟨W, hW⟩ := exists_conjDiag_freshEigenvalue hH
  set lam := fun k => freshEigenvalue H k
  set Wm := (W : Matrix (Fin m) (Fin m) ℂ)
  have hWW : star Wm * Wm = 1 := Matrix.UnitaryGroup.star_mul_self W
  have hHH : H * H = Wm * (Matrix.diagonal (fun i => (lam i : ℂ)) *
      Matrix.diagonal (fun i => (lam i : ℂ))) * star Wm := by
    rw [hW]
    simp only [conjDiag, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star Wm) Wm, hWW, Matrix.one_mul]
  rw [hHH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWW, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]

theorem trace_borderHerm (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (a : ℝ) :
    (borderHerm M v a).trace = M.trace + a := by
  simp [Matrix.trace, Fin.sum_univ_castSucc, borderHerm]

theorem trace_borderHerm_mul_diagonal (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (a : ℝ)
    (d : Fin (n + 1) → ℝ) :
    (borderHerm M v a * Matrix.diagonal fun i => (d i : ℂ)).trace =
      (M * Matrix.diagonal fun i : Fin n => (d i.castSucc : ℂ)).trace +
        (a : ℂ) * (d (Fin.last n) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_diagonal, Fin.sum_univ_castSucc, borderHerm]

/-- The border weight: `w_d(B) = w_{d'}(M) β(λ(B), λ(M))` for `B = [[M, v], [v*, a]]`, with
`β(λ, μ) = e^{−Σλ²/2S + d_nΣλ/S} e^{Σμ²/2S − d_nΣμ/S}`. -/
theorem sourceWeight_borderHerm (S : ℝ≥0) (hS : 0 < S) (d : Fin (n + 1) → ℝ)
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (v : Fin n → ℂ) (a : ℝ) :
    Real.exp ((-(borderHerm M v a * borderHerm M v a).trace.re +
        2 * (borderHerm M v a * Matrix.diagonal fun i => (d i : ℂ)).trace.re) / (2 * (S : ℝ))) =
      Real.exp ((-(M * M).trace.re +
          2 * (M * Matrix.diagonal fun i : Fin n => (d i.castSucc : ℂ)).trace.re) / (2 * (S : ℝ))) *
        (Real.exp (-(∑ i, freshEigenvalue (borderHerm M v a) i ^ 2) / (2 * (S : ℝ)) +
            d (Fin.last n) * (∑ i, freshEigenvalue (borderHerm M v a) i) / (S : ℝ)) *
          Real.exp ((∑ i, freshEigenvalue M i ^ 2) / (2 * (S : ℝ)) -
            d (Fin.last n) * (∑ i, freshEigenvalue M i) / (S : ℝ))) := by
  have hB := isHermitian_borderHerm hM v a
  have hSR : (S : ℝ) ≠ 0 := (NNReal.coe_pos.2 hS).ne'
  have ha : a = (∑ i, freshEigenvalue (borderHerm M v a) i) - ∑ i, freshEigenvalue M i := by
    have h := congrArg Complex.re (trace_borderHerm M v a)
    rw [trace_re_eq_sum_freshEigenvalue hB, Complex.add_re, trace_re_eq_sum_freshEigenvalue hM,
      Complex.ofReal_re] at h
    linarith
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [trace_sq_re_eq_sum_freshEigenvalue hB, trace_sq_re_eq_sum_freshEigenvalue hM,
    trace_borderHerm_mul_diagonal, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  generalize (∑ i, freshEigenvalue (borderHerm M v a) i ^ 2) = qB
  generalize (∑ i, freshEigenvalue (borderHerm M v a) i) = sB at ha ⊢
  rw [ha]
  field_simp
  ring

/-!
## Continuity and measurability
-/

theorem continuous_sourceWeight {m : ℕ} (S : ℝ≥0) (d : Fin m → ℝ) :
    Continuous fun H : Matrix (Fin m) (Fin m) ℂ => Real.exp ((-(H * H).trace.re +
      2 * (H * Matrix.diagonal fun i => (d i : ℂ)).trace.re) / (2 * (S : ℝ))) := by
  have h1 : Continuous fun H : Matrix (Fin m) (Fin m) ℂ => H * H :=
    continuous_id.matrix_mul continuous_id
  have h2 : Continuous fun H : Matrix (Fin m) (Fin m) ℂ =>
      H * Matrix.diagonal fun i => (d i : ℂ) :=
    continuous_id.matrix_mul continuous_const
  exact Real.continuous_exp.comp (((Complex.continuous_re.comp h1.matrix_trace).neg.add
    (continuous_const.mul (Complex.continuous_re.comp h2.matrix_trace))).div_const _)

theorem continuous_expDet {m : ℕ} (S : ℝ≥0) (d : Fin m → ℝ) :
    Continuous fun lam : Fin m → ℝ => expDet S d lam := by
  unfold expDet
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  exact Real.continuous_exp.comp (((continuous_apply i).mul continuous_const).div_const _)

theorem continuous_orderedProfile {m : ℕ} (S : ℝ≥0) (d : Fin m → ℝ) :
    Continuous fun lam : Fin m → ℝ => orderedProfile S d lam := by
  unfold orderedProfile
  refine ((continuous_vandermonde.div_const _).mul (continuous_expDet S d)).mul ?_
  exact Real.continuous_exp.comp ((continuous_finsetSum _ fun i _ =>
    (continuous_apply i).pow 2).neg.div_const _)

theorem measurable_lintegral_interlaceSet
    {F : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun μ => ∫⁻ lam in interlaceSet μ, F (μ, lam) := by
  have h := (hF.indicator (measurableSet_interlacePairs (n := n))).lintegral_prod_right'
    (ν := volume)
  have heq : (fun μ => ∫⁻ lam in interlaceSet μ, F (μ, lam)) =
      fun μ => ∫⁻ lam, (interlacePairs n).indicator F (μ, lam) := by
    funext μ
    rw [← lintegral_indicator (show MeasurableSet (interlaceSet μ) from
      measurableSet_interlacePairs.preimage measurable_prodMk_left)]
    rfl
  rw [heq]
  exact h

/-!
## The general-weight swap over `{λ ≻ μ}`
-/

/-- Tonelli over `{(μ, λ) : λ ≻ μ}` for a general weight:
`∫_{𝒞_n} ∫_{λ ≻ μ} F(μ, λ) dλ dμ = ∫_{𝒞_{n+1}} ∫_{box λ} F(μ, λ) dμ dλ`. -/
theorem lintegral_interlace_swap_general
    {F : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ μ in weylChamber n, ∫⁻ lam in interlaceSet μ, F (μ, lam) =
      ∫⁻ lam in weylChamber (n + 1), ∫⁻ μ in interlaceBox lam, F (μ, lam) := by
  set G := (interlacePairs n).indicator F with hG
  have hGm : Measurable G := hF.indicator measurableSet_interlacePairs
  have hL : ∀ μ : Fin n → ℝ, (weylChamber n).indicator
      (fun μ => ∫⁻ lam in interlaceSet μ, F (μ, lam)) μ = ∫⁻ lam, G (μ, lam) := by
    intro μ
    have hS : MeasurableSet (interlaceSet μ) :=
      measurableSet_interlacePairs.preimage measurable_prodMk_left
    have hGμ : (fun lam => G (μ, lam)) = (interlaceSet μ).indicator fun lam => F (μ, lam) := by
      funext lam
      simp only [hG, Set.indicator]
      rfl
    rw [hGμ, lintegral_indicator hS]
    by_cases hμ : μ ∈ weylChamber n
    · rw [Set.indicator_of_mem hμ]
    · rw [Set.indicator_of_notMem hμ]
      have hempty : interlaceSet μ = ∅ :=
        Set.eq_empty_of_forall_notMem fun lam hlam => hμ (strictMono_of_interlace hlam)
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
  have hR : ∀ lam : Fin (n + 1) → ℝ, ∫⁻ μ, G (μ, lam) = (weylChamber (n + 1)).indicator
      (fun lam => ∫⁻ μ in interlaceBox lam, F (μ, lam)) lam := by
    intro lam
    have hGl : (fun μ => G (μ, lam)) = (interlaceBox lam).indicator fun μ => F (μ, lam) := by
      funext μ
      by_cases hμ : μ ∈ interlaceBox lam
      · have hmem : (μ, lam) ∈ interlacePairs n := fun i => hμ i (Set.mem_univ _)
        simp only [hG, Set.indicator_of_mem hmem, Set.indicator_of_mem hμ]
      · have hmem : (μ, lam) ∉ interlacePairs n := fun h => hμ fun i _ => h i
        simp only [hG, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hμ]
    rw [hGl, lintegral_indicator (measurableSet_interlaceBox lam)]
    by_cases hlam : lam ∈ weylChamber (n + 1)
    · rw [Set.indicator_of_mem hlam]
    · rw [Set.indicator_of_notMem hlam, interlaceBox_eq_empty hlam, Measure.restrict_empty,
        lintegral_zero_measure]
  rw [← lintegral_indicator isOpen_weylChamber.measurableSet]
  simp_rw [hL]
  rw [lintegral_lintegral_swap (f := fun μ lam => G (μ, lam)) hGm.aemeasurable]
  simp_rw [hR]
  rw [lintegral_indicator isOpen_weylChamber.measurableSet]

/-!
## Corners with a repeated eigenvalue are null
-/

/-- If the eigenvalues of `H(y)` under a positive weight have a law supported on the chamber,
then `λ(H(y))` lies in the open chamber for Lebesgue-a.e. `y`. -/
theorem ae_mem_weylChamber_of_law {m : ℕ} {w : (HermCoord m → ℝ) → ℝ} (hwm : Measurable w)
    (hw : ∀ y, 0 < w y) {C : ℝ} {ρ : (Fin m → ℝ) → ℝ≥0∞}
    (hlaw : ∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (fun k => freshEigenvalue (hermOfCoord y) k) * ENNReal.ofReal (w y) =
        ENNReal.ofReal C * ∫⁻ lam in weylChamber m, g lam * ρ lam) :
    ∀ᵐ y : HermCoord m → ℝ, (fun k => freshEigenvalue (hermOfCoord y) k) ∈ weylChamber m := by
  have hch : MeasurableSet (weylChamber m) := isOpen_weylChamber.measurableSet
  have hgm : Measurable ((weylChamber m)ᶜ.indicator (1 : (Fin m → ℝ) → ℝ≥0∞)) :=
    measurable_one.indicator hch.compl
  have h := hlaw _ hgm
  have hz : ∫⁻ lam in weylChamber m, (weylChamber m)ᶜ.indicator 1 lam * ρ lam = 0 := by
    rw [setLIntegral_congr_fun hch (g := fun _ => 0) fun lam hl => by
      simp [Set.indicator_of_notMem (show lam ∉ (weylChamber m)ᶜ from fun h => h hl)]]
    exact lintegral_zero
  rw [hz, mul_zero] at h
  have hm : Measurable fun y : HermCoord m → ℝ =>
      (weylChamber m)ᶜ.indicator 1 (fun k => freshEigenvalue (hermOfCoord y) k) *
        ENNReal.ofReal (w y) :=
    (hgm.comp measurable_freshEigs_hermOfCoord).mul (ENNReal.measurable_ofReal.comp hwm)
  filter_upwards [(lintegral_eq_zero_iff hm).1 h] with y hy
  by_contra hne
  have h1 := mul_eq_zero.1 hy
  rcases h1 with h1 | h1
  · simp [Set.indicator_of_mem (show _ ∈ (weylChamber m)ᶜ from hne)] at h1
  · exact (ENNReal.ofReal_pos.2 (hw y)).ne' h1

/-!
## The box integral of the profile
-/

/-- For `λ` in the open chamber and any constant `c`,
`∫_{box λ} (Δ(λ)/Δ(μ)) c β(λ, μ) Φ_n(μ) dμ = c S^n Φ_{n+1}(λ)`. -/
theorem lintegral_interlaceBox_profile (S : ℝ≥0) (hS : 0 < S) (d : Fin (n + 1) → ℝ)
    (hd : StrictMono d) {lam : Fin (n + 1) → ℝ} (hlam : lam ∈ weylChamber (n + 1)) (c : ℝ≥0∞) :
    ∫⁻ μ in interlaceBox lam, ENNReal.ofReal (vandermonde lam / vandermonde μ) *
        (c * ENNReal.ofReal (Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) +
            d (Fin.last n) * (∑ i, lam i) / (S : ℝ)) *
          Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ)))) *
        ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ) =
      c * ENNReal.ofReal ((S : ℝ) ^ n * orderedProfile S d lam) := by
  have hd' : StrictMono fun j : Fin n => d j.castSucc := hd.comp Fin.strictMono_castSucc
  have hVl := vandermonde_pos hlam
  have hbox : ∀ μ ∈ interlaceBox lam, μ ∈ weylChamber n := fun μ hμ =>
    strictMono_of_mem_interlaceBox (show StrictMono lam from hlam).monotone hμ
  have hE2c : Continuous fun μ : Fin n → ℝ =>
      Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ)) :=
    Real.continuous_exp.comp (((continuous_finsetSum _ fun i _ =>
      (continuous_apply i).pow 2).div_const _).sub
        ((continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_apply i)).div_const _))
  have hfm : Measurable fun μ : Fin n → ℝ =>
      ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ / vandermonde μ *
        Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ))) :=
    ENNReal.measurable_ofReal.comp (((continuous_orderedProfile S _).measurable.div
      continuous_vandermonde.measurable).mul hE2c.measurable)
  have hpt : ∀ μ ∈ interlaceBox lam, ENNReal.ofReal (vandermonde lam / vandermonde μ) *
        (c * ENNReal.ofReal (Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) +
            d (Fin.last n) * (∑ i, lam i) / (S : ℝ)) *
          Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ)))) *
        ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ) =
      c * ENNReal.ofReal (vandermonde lam * Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) +
            d (Fin.last n) * (∑ i, lam i) / (S : ℝ))) *
        ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ / vandermonde μ *
          Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ))) := by
    intro μ hμ
    have hVm := vandermonde_pos (hbox μ hμ)
    have h1 : 0 ≤ vandermonde lam / vandermonde μ := (div_pos hVl hVm).le
    rw [mul_assoc c, ← ENNReal.ofReal_mul (by positivity),
      show ENNReal.ofReal (vandermonde lam / vandermonde μ) * (c * ENNReal.ofReal
        (Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) + d (Fin.last n) * (∑ i, lam i) / (S : ℝ)) *
          Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ)))) *
        ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ) =
      c * (ENNReal.ofReal (vandermonde lam / vandermonde μ) * ENNReal.ofReal
        (Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) + d (Fin.last n) * (∑ i, lam i) / (S : ℝ)) *
          Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ))) *
        ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ)) by ring,
      ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  rw [setLIntegral_congr_fun (measurableSet_interlaceBox lam) hpt, lintegral_const_mul _ hfm]
  have hK : IsCompact (Set.univ.pi fun i : Fin n => Set.Icc (lam i.castSucc) (lam i.succ)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : interlaceBox lam ⊆
      Set.univ.pi fun i : Fin n => Set.Icc (lam i.castSucc) (lam i.succ) :=
    Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self
  have hhc : Continuous fun μ : Fin n → ℝ => (Matrix.of fun i j =>
      Real.exp (μ i * ((d j.castSucc - d (Fin.last n)) / (S : ℝ)))).det /
        vandermonde fun j => d j.castSucc := by
    refine (Continuous.matrix_det (continuous_matrix fun i j => ?_)).div_const _
    exact Real.continuous_exp.comp ((continuous_apply i).mul continuous_const)
  have hI : IntegrableOn (fun μ : Fin n → ℝ => orderedProfile S (fun j => d j.castSucc) μ /
      vandermonde μ * Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) -
        d (Fin.last n) * (∑ i, μ i) / (S : ℝ))) (interlaceBox lam) := by
    refine IntegrableOn.congr_fun ((hhc.continuousOn.integrableOn_compact hK).mono_set hsub)
      (fun μ hμ => ?_) (measurableSet_interlaceBox lam)
    exact (orderedProfile_div_vandermonde S hS _ _ (hbox μ hμ)).symm
  have hnn : ∀ᵐ μ ∂(volume.restrict (interlaceBox lam)),
      0 ≤ orderedProfile S (fun j => d j.castSucc) μ / vandermonde μ *
        Real.exp ((∑ i, μ i ^ 2) / (2 * (S : ℝ)) - d (Fin.last n) * (∑ i, μ i) / (S : ℝ)) :=
    ae_restrict_of_forall_mem (measurableSet_interlaceBox lam) fun μ hμ =>
      mul_nonneg (div_nonneg (profileNonneg_holds S hS _ hd' μ (hbox μ hμ))
        (vandermonde_pos (hbox μ hμ)).le) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn, mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← orderedProfile_succ_eq S hS d hd hlam]

/-!
## The source eigenvalue law
-/

/-- **C1, the source eigenvalue law on Lebesgue coordinates.** For `S > 0` and `StrictMono d`
there is `c > 0` such that for every measurable `g ≥ 0`, with `D = diag(d)`,
`∫ g(λ(H(y))) e^{(−Re tr H(y)² + 2 Re tr(H(y) D))/(2S)} dy = c ∫_𝒞 g(λ) Φ_n(λ) dλ`
(Lebesgue measure on `HermCoord n → ℝ` and on the open chamber). -/
theorem sourceEigenLaw (n : ℕ) (S : ℝ≥0) (hS : 0 < S) (d : Fin n → ℝ) (hd : StrictMono d) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : (Fin n → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ y : HermCoord n → ℝ, g (fun k => freshEigenvalue (hermOfCoord y) k) *
          ENNReal.ofReal (Real.exp ((-(hermOfCoord y * hermOfCoord y).trace.re +
            2 * (hermOfCoord y * Matrix.diagonal fun i => (d i : ℂ)).trace.re) /
              (2 * (S : ℝ)))) =
        ENNReal.ofReal c *
          ∫⁻ lam in weylChamber n, g lam * ENNReal.ofReal (orderedProfile S d lam) := by
  induction n with
  | zero =>
    refine ⟨1, one_pos, fun g hg => ?_⟩
    have hch : weylChamber 0 = Set.univ :=
      Set.eq_univ_of_forall fun lam => fun i => Fin.elim0 i
    rw [hch, Measure.restrict_univ, lintegral_unique, lintegral_unique]
    simp only [orderedProfile_zero, volume_pi, Measure.pi_univ, Finset.univ_eq_empty,
      Finset.prod_empty, ENNReal.ofReal_one, one_mul, mul_one]
    have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, M.trace = 0 := fun M => by simp [Matrix.trace]
    simp only [h0, Complex.zero_re, neg_zero, mul_zero, add_zero, zero_div, Real.exp_zero,
      ENNReal.ofReal_one, mul_one]
    exact congrArg g (Subsingleton.elim _ _)
  | succ n ih =>
    have hd' : StrictMono fun j : Fin n => d j.castSucc := hd.comp Fin.strictMono_castSucc
    obtain ⟨c', hc', hlaw⟩ := ih (fun j => d j.castSucc) hd'
    have hB : BorderEigenLawStatement :=
      borderEigenLaw_of_diagonal complexUnitaryInvariance diagonalBorderLaw_holds
    have hSR : (0 : ℝ) < S := NNReal.coe_pos.2 hS
    refine ⟨Real.pi ^ n * c' * (S : ℝ) ^ n, by positivity, fun g hg => ?_⟩
    have hβc : Continuous fun p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) =>
        Real.exp (-(∑ i, p.2 i ^ 2) / (2 * (S : ℝ)) + d (Fin.last n) * (∑ i, p.2 i) / (S : ℝ)) *
          Real.exp ((∑ i, p.1 i ^ 2) / (2 * (S : ℝ)) -
            d (Fin.last n) * (∑ i, p.1 i) / (S : ℝ)) := by
      have h2 : Continuous fun p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) => p.2 := continuous_snd
      have h1 : Continuous fun p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) => p.1 := continuous_fst
      refine (Real.continuous_exp.comp ?_).mul (Real.continuous_exp.comp ?_)
      · exact ((continuous_finsetSum _ fun i _ =>
          ((continuous_apply i).comp h2).pow 2).neg.div_const _).add
            ((continuous_const.mul (continuous_finsetSum _ fun i _ =>
              (continuous_apply i).comp h2)).div_const _)
      · exact ((continuous_finsetSum _ fun i _ => ((continuous_apply i).comp h1).pow 2).div_const
          _).sub ((continuous_const.mul (continuous_finsetSum _ fun i _ =>
            (continuous_apply i).comp h1)).div_const _)
    set F : (Fin n → ℝ) × (Fin (n + 1) → ℝ) → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (vandermonde p.2 / vandermonde p.1) * (g p.2 * ENNReal.ofReal
        (Real.exp (-(∑ i, p.2 i ^ 2) / (2 * (S : ℝ)) + d (Fin.last n) * (∑ i, p.2 i) / (S : ℝ)) *
          Real.exp ((∑ i, p.1 i ^ 2) / (2 * (S : ℝ)) -
            d (Fin.last n) * (∑ i, p.1 i) / (S : ℝ)))) with hFdef
    have hFm : Measurable F :=
      (ENNReal.measurable_ofReal.comp ((continuous_vandermonde.measurable.comp measurable_snd).div
        (continuous_vandermonde.measurable.comp measurable_fst))).mul
        ((hg.comp measurable_snd).mul (ENNReal.measurable_ofReal.comp hβc.measurable))
    have hPm := measurable_lintegral_interlaceSet hFm
    have hGm : Measurable fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ =>
        g (fun k => freshEigenvalue B k) * ENNReal.ofReal (Real.exp ((-(B * B).trace.re +
          2 * (B * Matrix.diagonal fun i => (d i : ℂ)).trace.re) / (2 * (S : ℝ)))) :=
      (hg.comp BlockBand.DeterminantScore.EigenDensity.measurable_freshEigs).mul
        (ENNReal.measurable_ofReal.comp (continuous_sourceWeight S d).measurable)
    have hw'm : Measurable fun y : HermCoord n → ℝ =>
        Real.exp ((-(hermOfCoord y * hermOfCoord y).trace.re +
          2 * (hermOfCoord y * Matrix.diagonal fun i : Fin n => (d i.castSucc : ℂ)).trace.re) /
            (2 * (S : ℝ))) :=
      ((continuous_sourceWeight S _).comp continuous_hermOfCoord).measurable
    have hae := ae_mem_weylChamber_of_law hw'm (fun y => Real.exp_pos _) hlaw
    -- the border integral at a fixed corner
    have hstep : ∀ y : HermCoord n → ℝ,
        (fun k => freshEigenvalue (hermOfCoord y) k) ∈ weylChamber n →
        ∫⁻ v : Fin n → ℂ, ∫⁻ a : ℝ,
            g (fun k => freshEigenvalue (borderHerm (hermOfCoord y) v a) k) *
              ENNReal.ofReal (Real.exp ((-(borderHerm (hermOfCoord y) v a *
                borderHerm (hermOfCoord y) v a).trace.re + 2 * (borderHerm (hermOfCoord y) v a *
                  Matrix.diagonal fun i => (d i : ℂ)).trace.re) / (2 * (S : ℝ)))) =
          ENNReal.ofReal (Real.pi ^ n) *
            ((∫⁻ lam in interlaceSet (fun k => freshEigenvalue (hermOfCoord y) k),
              F ((fun k => freshEigenvalue (hermOfCoord y) k), lam)) *
            ENNReal.ofReal (Real.exp ((-(hermOfCoord y * hermOfCoord y).trace.re +
              2 * (hermOfCoord y * Matrix.diagonal fun i : Fin n => (d i.castSucc : ℂ)).trace.re) /
                (2 * (S : ℝ))))) := by
      intro y hy
      have hM := isHermitian_hermOfCoord y
      set M := hermOfCoord y
      set μ0 := fun k => freshEigenvalue M k with hμ0
      set wM := Real.exp ((-(M * M).trace.re +
        2 * (M * Matrix.diagonal fun i : Fin n => (d i.castSucc : ℂ)).trace.re) / (2 * (S : ℝ)))
      have hpt : ∀ v a, g (fun k => freshEigenvalue (borderHerm M v a) k) *
          ENNReal.ofReal (Real.exp ((-(borderHerm M v a * borderHerm M v a).trace.re +
            2 * (borderHerm M v a * Matrix.diagonal fun i => (d i : ℂ)).trace.re) /
              (2 * (S : ℝ)))) =
          ENNReal.ofReal wM * (fun lam => g lam * ENNReal.ofReal
            (Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) + d (Fin.last n) * (∑ i, lam i) /
              (S : ℝ)) * Real.exp ((∑ i, μ0 i ^ 2) / (2 * (S : ℝ)) -
                d (Fin.last n) * (∑ i, μ0 i) / (S : ℝ))))
            (fun k => freshEigenvalue (borderHerm M v a) k) := by
        intro v a
        rw [sourceWeight_borderHerm S hS d hM v a, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      simp_rw [hpt]
      have hgβ : Measurable fun lam : Fin (n + 1) → ℝ => g lam * ENNReal.ofReal
          (Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)) + d (Fin.last n) * (∑ i, lam i) /
            (S : ℝ)) * Real.exp ((∑ i, μ0 i ^ 2) / (2 * (S : ℝ)) -
              d (Fin.last n) * (∑ i, μ0 i) / (S : ℝ))) :=
        hg.mul (ENNReal.measurable_ofReal.comp
          (hβc.comp (continuous_const.prodMk continuous_id)).measurable)
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [hB n _ hgβ M hM hy, interlaceAverage]
      ring
    calc _ = ∫⁻ y : HermCoord n → ℝ, ∫⁻ v : Fin n → ℂ, ∫⁻ a : ℝ,
            g (fun k => freshEigenvalue (borderHerm (hermOfCoord y) v a) k) *
              ENNReal.ofReal (Real.exp ((-(borderHerm (hermOfCoord y) v a *
                borderHerm (hermOfCoord y) v a).trace.re + 2 * (borderHerm (hermOfCoord y) v a *
                  Matrix.diagonal fun i => (d i : ℂ)).trace.re) / (2 * (S : ℝ)))) :=
          cornerFubini n _ hGm
      _ = ∫⁻ y : HermCoord n → ℝ, ENNReal.ofReal (Real.pi ^ n) *
            ((fun μ => ∫⁻ lam in interlaceSet μ, F (μ, lam))
              (fun k => freshEigenvalue (hermOfCoord y) k) *
            ENNReal.ofReal (Real.exp ((-(hermOfCoord y * hermOfCoord y).trace.re +
              2 * (hermOfCoord y * Matrix.diagonal fun i : Fin n => (d i.castSucc : ℂ)).trace.re) /
                (2 * (S : ℝ))))) := lintegral_congr_ae (hae.mono hstep)
      _ = ENNReal.ofReal (Real.pi ^ n) * (ENNReal.ofReal c' * ∫⁻ μ in weylChamber n,
            (∫⁻ lam in interlaceSet μ, F (μ, lam)) *
              ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ)) := by
          have hm : Measurable fun y : HermCoord n → ℝ =>
              (fun μ => ∫⁻ lam in interlaceSet μ, F (μ, lam))
                (fun k => freshEigenvalue (hermOfCoord y) k) *
              ENNReal.ofReal (Real.exp ((-(hermOfCoord y * hermOfCoord y).trace.re +
                2 * (hermOfCoord y * Matrix.diagonal fun i : Fin n =>
                  (d i.castSucc : ℂ)).trace.re) / (2 * (S : ℝ)))) :=
            (hPm.comp measurable_freshEigs_hermOfCoord).mul (ENNReal.measurable_ofReal.comp hw'm)
          rw [lintegral_const_mul _ hm, hlaw _ hPm]
      _ = ENNReal.ofReal (Real.pi ^ n) * (ENNReal.ofReal c' * ∫⁻ lam in weylChamber (n + 1),
            ∫⁻ μ in interlaceBox lam,
              F (μ, lam) * ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) μ)) := by
          have hm : Measurable fun p : (Fin n → ℝ) × (Fin (n + 1) → ℝ) =>
              F p * ENNReal.ofReal (orderedProfile S (fun j => d j.castSucc) p.1) :=
            hFm.mul (ENNReal.measurable_ofReal.comp
              ((continuous_orderedProfile S _).measurable.comp measurable_fst))
          rw [← lintegral_interlace_swap_general hm]
          congr 2
          refine lintegral_congr fun μ => ?_
          exact (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
      _ = ENNReal.ofReal (Real.pi ^ n) * (ENNReal.ofReal c' * ∫⁻ lam in weylChamber (n + 1),
            g lam * ENNReal.ofReal ((S : ℝ) ^ n * orderedProfile S d lam)) := by
          congr 2
          refine setLIntegral_congr_fun isOpen_weylChamber.measurableSet fun lam hlam => ?_
          exact lintegral_interlaceBox_profile S hS d hd hlam (g lam)
      _ = _ := by
          simp_rw [ENNReal.ofReal_mul (pow_nonneg hSR.le n), mul_left_comm (g _)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring

/-!
## The ordered law
-/

theorem trace_sub_diagonal_sq_re {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℝ) :
    ((H - Matrix.diagonal fun i => (d i : ℂ)) * (H - Matrix.diagonal fun i => (d i : ℂ))).trace.re =
      (H * H).trace.re - 2 * (H * Matrix.diagonal fun i => (d i : ℂ)).trace.re +
        ∑ i, d i ^ 2 := by
  set K : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => (d i : ℂ)
  have hKK : (K * K).trace.re = ∑ i, d i ^ 2 := by
    simp only [K, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
  rw [show (H - K) * (H - K) = H * H - H * K - K * H + K * K by noncomm_ring,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm K H,
    Complex.add_re, Complex.sub_re, Complex.sub_re, hKK]
  ring

/-- **C3, the ordered law, from the coordinate bridge C0.** -/
theorem orderedLaw_of_bridge (hB : CoordinateBridgeStatement) : OrderedLawStatement := by
  intro N S hS d hd
  obtain ⟨c, hc, hlaw⟩ := sourceEigenLaw N S hS d hd
  have hSR : (0 : ℝ) < S := NNReal.coe_pos.2 hS
  have hKh : (Matrix.diagonal fun i => (d i : ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  have hcN := BlockBand.DeterminantScore.EigenDensity.hermGaussianConst_pos (m := N) hS
  set κ := BlockBand.DeterminantScore.EigenDensity.hermGaussianConst N S *
    Real.exp (-(∑ i, d i ^ 2) / (2 * (S : ℝ))) with hκ
  have hκpos : 0 < κ := mul_pos hcN (Real.exp_pos _)
  refine ⟨κ * c, mul_pos hκpos hc, fun g hg => ?_⟩
  rw [hB S d g hg, BlockBand.DeterminantScore.EigenDensity.lintegral_orderedEigs_eq hS hKh hg]
  have hpt : ∀ y : HermCoord N → ℝ,
      g (fun k => freshEigenvalue (hermOfCoord y) k) *
        ENNReal.ofReal (BlockBand.DeterminantScore.EigenDensity.hermGaussianConst N S *
          Real.exp (-((hermOfCoord y - Matrix.diagonal fun i => (d i : ℂ)) *
            (hermOfCoord y - Matrix.diagonal fun i => (d i : ℂ))).trace.re / (2 * (S : ℝ)))) =
      ENNReal.ofReal κ * (g (fun k => freshEigenvalue (hermOfCoord y) k) *
        ENNReal.ofReal (Real.exp ((-(hermOfCoord y * hermOfCoord y).trace.re +
          2 * (hermOfCoord y * Matrix.diagonal fun i => (d i : ℂ)).trace.re) /
            (2 * (S : ℝ))))) := by
    intro y
    rw [mul_left_comm, ← ENNReal.ofReal_mul hκpos.le, hκ, mul_assoc, ← Real.exp_add,
      trace_sub_diagonal_sq_re]
    congr 4
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlaw g hg, ← mul_assoc,
    ← ENNReal.ofReal_mul hκpos.le]

end BlockBand.Native.Johansson
