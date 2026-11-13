module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneMixedPairingAssembly

/-!
# Dimension-free horizontal boundary modulus for the CEH cutoff

The regular-boundary contract bounds the `L²` operator norm of its matrix
 derivative.  This module transfers that bound, without a dimension factor, to
 the normalized scalar MDE mean and then to every scalar spectral entry.  The
 source-window separation may therefore be inserted with its exact factor
 `2 N^(β-1)`.  The same file extracts the sharp linear vertical modulus hidden
 in the integrated first-exit argument.  Closing the published two-energy
 cutoff now requires only assembling these two displayed moduli with the exact
 canonical-spacing equation and the source quantifier order; no dimensional
 loss or missing matrix-to-entry coercion remains.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Every matrix entry is bounded by the `L²` operator norm used by the
published regular-window interface. -/
theorem norm_matrix_entry_le_localETHNorm {N : ℕ}
    (M : LocalETHMatrix N) (i j : Fin N) :
    ‖M i j‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (Pi.single j 1)
  let y : EuclideanSpace ℂ (Fin N) :=
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M e
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop := (Matrix.toEuclideanCLM
    (n := Fin N) (𝕜 := ℂ) M).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hyi : y.ofLp i = M i j := by simp [y, e]
  calc
    ‖M i j‖ = ‖y.ofLp i‖ := congrArg norm hyi.symm
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M‖ * ‖e‖ := hop
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, he, mul_one]

/-- The normalized trace has operator norm at most one.  The normalization by
`N` exactly cancels the sum over the `N` diagonal entries. -/
theorem norm_normalizedTrace_le_localETHNorm
    {N : ℕ} (hN : 0 < N) (M : LocalETHMatrix N) :
    ‖Conventions.normalizedTrace M‖ ≤ ‖M‖ := by
  unfold Conventions.normalizedTrace
  change ‖(N : ℂ)⁻¹ * ∑ i : Fin N, M i i‖ ≤ ‖M‖
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ i : Fin N, M i i‖ ≤ (N : ℝ) * ‖M‖ := by
    calc
      ‖∑ i : Fin N, M i i‖ ≤ ∑ i : Fin N, ‖M i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, ‖M‖ := by
        gcongr with i
        exact norm_matrix_entry_le_localETHNorm M i i
      _ = (N : ℝ) * ‖M‖ := by simp
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    (N : ℝ)⁻¹ * ‖∑ i : Fin N, M i i‖ ≤
        (N : ℝ)⁻¹ * ((N : ℝ) * ‖M‖) := by
      gcongr
    _ = ‖M‖ := by field_simp [hNR]

/-- Entrywise differentiability of the matrix boundary witness differentiates
its normalized trace with no change of normalization. -/
theorem hasDerivAt_normalizedTrace_of_matrixDeriv
    {N : ℕ} {Mb Mb' : ℝ → LocalETHMatrix N} {x : ℝ}
    (hderiv : HasLocalETHMatrixDerivAt Mb (Mb' x) x) :
    HasDerivAt (fun t => Conventions.normalizedTrace (Mb t))
      (Conventions.normalizedTrace (Mb' x)) x := by
  unfold Conventions.normalizedTrace Matrix.trace
  convert (HasDerivAt.const_mul (c := (N : ℂ)⁻¹)
    (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N)))
      (fun i _ => hderiv i i))) using 1 <;> simp

/-- Mean-value transfer of the matrix derivative bound to the
normalized scalar MDE mean.  The constant is exactly `K`, independent of
`N`. -/
theorem norm_normalizedTrace_sub_le_of_regularDerivative
    {N : ℕ} (hN : 0 < N) {E₀ r K x y : ℝ}
    {Mb Mb' : ℝ → LocalETHMatrix N}
    (hxy : x ≤ y)
    (hseg : Icc x y ⊆ Ioo (E₀ - r) (E₀ + r))
    (hderiv : ∀ t ∈ Ioo (E₀ - r) (E₀ + r),
      HasLocalETHMatrixDerivAt Mb (Mb' t) t)
    (hbound : ∀ t ∈ Ioo (E₀ - r) (E₀ + r), ‖Mb' t‖ ≤ K) :
    ‖Conventions.normalizedTrace (Mb y) -
      Conventions.normalizedTrace (Mb x)‖ ≤ K * (y - x) := by
  let m : ℝ → ℂ := fun t => Conventions.normalizedTrace (Mb t)
  let m' : ℝ → ℂ := fun t => Conventions.normalizedTrace (Mb' t)
  have hd : ∀ t ∈ Icc x y, HasDerivWithinAt m (m' t) (Icc x y) t := by
    intro t ht
    exact (hasDerivAt_normalizedTrace_of_matrixDeriv
      (hderiv t (hseg ht))).hasDerivWithinAt
  have hb : ∀ t ∈ Icc x y, ‖m' t‖ ≤ K := by
    intro t ht
    exact (norm_normalizedTrace_le_localETHNorm hN (Mb' t)).trans
      (hbound t (hseg ht))
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb (convex_Icc x y) (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  simpa [m, m', Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy),
    mul_comm] using hmv

/-- The exact resolvent identity transfers the horizontal scalar-mean modulus
to every boundary spectral entry. -/
theorem norm_boundary_entry_sub_le_of_mean_modulus
    {N : ℕ} (f : DeformationSpectrum N) {s c x y K : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hK : 0 ≤ K) {mx my : ℂ}
    (himx : c ≤ mx.im) (himy : c ≤ my.im)
    (hmean : ‖my - mx‖ ≤ K * |y - x|) (i : Fin N) :
    ‖entry f s (y : ℂ) my i - entry f s (x : ℂ) mx i‖ ≤
      (1 + s * K) * |y - x| * (s * c)⁻¹ ^ 2 := by
  have hhx : s * c ≤ effectiveHeight s (x : ℂ) mx := by
    simp only [effectiveHeight, Complex.ofReal_im, zero_add]
    exact mul_le_mul_of_nonneg_left himx hs.le
  have hhy : s * c ≤ effectiveHeight s (y : ℂ) my := by
    simp only [effectiveHeight, Complex.ofReal_im, zero_add]
    exact mul_le_mul_of_nonneg_left himy hs.le
  have hsc : 0 < s * c := mul_pos hs hc
  have hdx := denominator_ne_zero f (hsc.trans_le hhx) i
  have hdy := denominator_ne_zero f (hsc.trans_le hhy) i
  have hid : entry f s (y : ℂ) my i - entry f s (x : ℂ) mx i =
      (((y : ℂ) - (x : ℂ)) + (s : ℂ) * (my - mx)) *
        entry f s (y : ℂ) my i * entry f s (x : ℂ) mx i := by
    unfold entry
    rw [inv_sub_inv' hdy hdx]
    ring
  rw [hid, norm_mul, norm_mul]
  have heY := (norm_entry_le_inv_effectiveHeight f (hsc.trans_le hhy) i).trans
    (inv_anti₀ hsc hhy)
  have heX := (norm_entry_le_inv_effectiveHeight f (hsc.trans_le hhx) i).trans
    (inv_anti₀ hsc hhx)
  have hfirst : ‖((y : ℂ) - (x : ℂ)) + (s : ℂ) * (my - mx)‖ ≤
      (1 + s * K) * |y - x| := by
    calc
      _ ≤ ‖(y : ℂ) - (x : ℂ)‖ + ‖(s : ℂ) * (my - mx)‖ := norm_add_le _ _
      _ = |y - x| + s * ‖my - mx‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        norm_cast
      _ ≤ |y - x| + s * (K * |y - x|) := by gcongr
      _ = (1 + s * K) * |y - x| := by ring
  calc
    _ ≤ (1 + s * K) * |y - x| * (s * c)⁻¹ * (s * c)⁻¹ := by
      have hcoef : 0 ≤ (1 + s * K) * |y - x| := by positivity
      gcongr
    _ = (1 + s * K) * |y - x| * (s * c)⁻¹ ^ 2 := by ring

/-- The checked-in regular-window derivative interface therefore gives the
required dimension-free horizontal boundary-entry modulus. -/
theorem regularBoundaryWindow_horizontalBoundaryEntryModulus
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s E₀ r c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K) :
    ∃ Mb _Mb' : ℝ → LocalETHMatrix N,
      ∀ x y : ℝ, x ≤ y → Icc x y ⊆ Ioo (E₀ - r) (E₀ + r) →
        ∀ i : Fin N,
          ‖entry (hermitianSpectrum hF) s (y : ℂ)
              (Conventions.normalizedTrace (Mb y)) i -
            entry (hermitianSpectrum hF) s (x : ℂ)
              (Conventions.normalizedTrace (Mb x)) i‖ ≤
            (1 + s * K) * |y - x| * (s * c)⁻¹ ^ 2 := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  refine ⟨Mb, Mb', ?_⟩
  intro x y hxy hseg i
  have hx := hseg (left_mem_Icc.mpr hxy)
  have hy := hseg (right_mem_Icc.mpr hxy)
  have hK : 0 ≤ K :=
    (norm_nonneg (Mb' x)).trans (hdata x hx).2.2.1
  apply norm_boundary_entry_sub_le_of_mean_modulus
    (hermitianSpectrum hF) hs hc hK
    (hdata x hx).2.2.2.1 (hdata y hy).2.2.2.1
  have hm := norm_normalizedTrace_sub_le_of_regularDerivative hN hxy hseg
    (fun t ht => (hdata t ht).2.1) (fun t ht => (hdata t ht).2.2.1)
  simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using hm

/-- Inserting the published source window retains its exact factor two. -/
theorem regularBoundaryWindow_sourceBoundaryEntryModulus
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s E₀ r c K β x y : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K)
    (hxy : x ≤ y) (hseg : Icc x y ⊆ Ioo (E₀ - r) (E₀ + r))
    (hx : |x - E₀| ≤ (N : ℝ) ^ (β - 1))
    (hy : |y - E₀| ≤ (N : ℝ) ^ (β - 1)) :
    ∃ Mb _Mb' : ℝ → LocalETHMatrix N, ∀ i : Fin N,
      ‖entry (hermitianSpectrum hF) s (y : ℂ)
          (Conventions.normalizedTrace (Mb y)) i -
        entry (hermitianSpectrum hF) s (x : ℂ)
          (Conventions.normalizedTrace (Mb x)) i‖ ≤
        (1 + s * K) * (2 * (N : ℝ) ^ (β - 1)) * (s * c)⁻¹ ^ 2 := by
  obtain ⟨Mb, Mb', hmod⟩ :=
    regularBoundaryWindow_horizontalBoundaryEntryModulus hF hN hs hc hregular
  refine ⟨Mb, Mb', fun i => (hmod x y hxy hseg i).trans ?_⟩
  have hsep := abs_sub_le_two_mul_rpow_of_sourceWindow hx hy
  have hxopen := hseg (left_mem_Icc.mpr hxy)
  obtain ⟨Mb₀, Mb₀', hdata⟩ := hregular.boundary
  have hK : 0 ≤ K := (norm_nonneg (Mb₀' x)).trans (hdata x hxopen).2.2.1
  have hcoef : 0 ≤ 1 + s * K := by positivity
  gcongr
  simpa [abs_sub_comm] using hsep

/-- The first-exit argument also yields its underlying sharp linear scalar
modulus at every height below the quantitative cutoff. -/
theorem upperBranch_linear_close_boundary_below_quantitativeIFTHeight
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s c x : ℝ} (hs : 0 < s) (hc : 0 < c)
    {m₀ : ℂ} (hm₀sol : IsSolution f s (x : ℂ) m₀)
    (hm₀im : c ≤ m₀.im)
    (hm₀stab : c ≤ ‖stabilityDenominator f s (x : ℂ) m₀‖)
    (hboundary : Tendsto
      (fun η : ℝ => upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds m₀))
    {η : ℝ} (hη : 0 < η) (hηH : η ≤ quantitativeIFTHeight s c) :
    ‖upperBranch hN f hs
      ((x : ℂ) + (η : ℂ) * Complex.I) - m₀‖ ≤
        8 * η / (s ^ 2 * c ^ 3) := by
  obtain ⟨hR, _hH, hRheight, hsmall, _hcontract⟩ :=
    quantitativeIFTRadius_height_spec hs hc
  let z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  let m : ℂ := upperBranch hN f hs z
  have hz : 0 < z.im := by simp [z, hη]
  have hmsol : IsSolution f s z m := upperBranch_isSolution hN f hs hz
  have hclose : ‖m - m₀‖ < quantitativeIFTRadius s c := by
    exact upperBranch_close_boundary_below_quantitativeIFTHeight
      hN f hs hc hm₀sol hm₀im hm₀stab hboundary η hη hηH
  have himdiff : |m.im - m₀.im| ≤ ‖m - m₀‖ := by
    simpa using Complex.abs_im_le_norm (m - m₀)
  have hmim : c / 2 ≤ m.im := by
    have hlower := neg_le_of_abs_le himdiff
    have hRc : quantitativeIFTRadius s c ≤ c / 2 := hRheight
    linarith
  have hheight : s * c / 2 ≤ effectiveHeight s z m := by
    simp only [effectiveHeight]
    have : 0 ≤ z.im := hz.le
    nlinarith
  have hheight₀ : s * c / 2 ≤ effectiveHeight s (x : ℂ) m₀ := by
    simp only [effectiveHeight, Complex.ofReal_im, zero_add]
    nlinarith
  have hzdist : ‖z - (x : ℂ)‖ = η := by
    simp [z, abs_of_pos hη]
  have hsmallη : s * (‖z - (x : ℂ)‖ + s * ‖m - m₀‖) *
      (s * c / 2)⁻¹ ^ 3 ≤ c / 2 := by
    apply le_trans _ hsmall
    gcongr
    · rw [hzdist]
      exact hηH
  have hboot := boundary_quantitativeIFT_bootstrap hN f hs hc
    hmsol hm₀sol hheight hheight₀ hm₀stab hsmallη
  simpa [m, z, hzdist, abs_of_pos hη] using hboot.2

/-- Consequently every positive-height scalar spectral entry has a fully
explicit dimension-free vertical modulus. -/
theorem norm_upperBranch_entry_sub_boundary_le
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s c x : ℝ} (hs : 0 < s) (hc : 0 < c)
    {m₀ : ℂ} (hm₀sol : IsSolution f s (x : ℂ) m₀)
    (hm₀im : c ≤ m₀.im)
    (hm₀stab : c ≤ ‖stabilityDenominator f s (x : ℂ) m₀‖)
    (hboundary : Tendsto
      (fun η : ℝ => upperBranch hN f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds m₀))
    {η : ℝ} (hη : 0 < η) (hηH : η ≤ quantitativeIFTHeight s c)
    (i : Fin N) :
    ‖entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
          (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)) i -
        entry f s (x : ℂ) m₀ i‖ ≤
      (η + s * (8 * η / (s ^ 2 * c ^ 3))) *
        (s * c / 2)⁻¹ * (s * c)⁻¹ := by
  let z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  let m : ℂ := upperBranch hN f hs z
  have hz : 0 < z.im := by simp [z, hη]
  have hlinear : ‖m - m₀‖ ≤ 8 * η / (s ^ 2 * c ^ 3) := by
    exact upperBranch_linear_close_boundary_below_quantitativeIFTHeight
      hN f hs hc hm₀sol hm₀im hm₀stab hboundary hη hηH
  have hclose := upperBranch_close_boundary_below_quantitativeIFTHeight
    hN f hs hc hm₀sol hm₀im hm₀stab hboundary η hη hηH
  have hspec := quantitativeIFTRadius_height_spec hs hc
  have himdiff : |m.im - m₀.im| ≤ ‖m - m₀‖ := by
    simpa using Complex.abs_im_le_norm (m - m₀)
  have hmim : c / 2 ≤ m.im := by
    have hlower := neg_le_of_abs_le himdiff
    linarith [hspec.2.2.1]
  have hh : s * c / 2 ≤ effectiveHeight s z m := by
    simp only [effectiveHeight]
    nlinarith
  have hh₀ : s * c ≤ effectiveHeight s (x : ℂ) m₀ := by
    simp only [effectiveHeight, Complex.ofReal_im, zero_add]
    exact mul_le_mul_of_nonneg_left hm₀im hs.le
  have hsc : 0 < s * c := by positivity
  have hsch : 0 < s * c / 2 := by positivity
  have hne := denominator_ne_zero f (hsch.trans_le hh) i
  have hne₀ := denominator_ne_zero f (hsc.trans_le hh₀) i
  have hid : entry f s z m i - entry f s (x : ℂ) m₀ i =
      (z - (x : ℂ) + (s : ℂ) * (m - m₀)) *
        entry f s z m i * entry f s (x : ℂ) m₀ i := by
    unfold entry
    rw [inv_sub_inv' hne hne₀]
    ring
  have he := (norm_entry_le_inv_effectiveHeight f (hsch.trans_le hh) i).trans
    (inv_anti₀ hsch hh)
  have he₀ := (norm_entry_le_inv_effectiveHeight f (hsc.trans_le hh₀) i).trans
    (inv_anti₀ hsc hh₀)
  rw [show entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
      (upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)) i =
      entry f s z m i by rfl, hid, norm_mul, norm_mul]
  have hfirst : ‖z - (x : ℂ) + (s : ℂ) * (m - m₀)‖ ≤
      η + s * (8 * η / (s ^ 2 * c ^ 3)) := by
    calc
      _ ≤ ‖z - (x : ℂ)‖ + ‖(s : ℂ) * (m - m₀)‖ := norm_add_le _ _
      _ = η + s * ‖m - m₀‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        simp [z, abs_of_pos hη]
      _ ≤ _ := by gcongr
  calc
    _ ≤ (η + s * (8 * η / (s ^ 2 * c ^ 3))) *
        (s * c / 2)⁻¹ * (s * c)⁻¹ := by
      gcongr

end CEHNative.BlockBand.CEH
