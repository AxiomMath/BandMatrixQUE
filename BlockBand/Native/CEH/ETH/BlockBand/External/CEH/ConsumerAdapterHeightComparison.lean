module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOnePublishedAdapter
public import BlockBand.Native.CEH.BlockBand.External.CEH.TypicalSpacingLocalETHAssembly

/-!
# Height comparison and auxiliary-loss conversion for the CEH consumer

Normalization: that of `Published.LocalETHInput` (normalized trace,
`Γ = Im M / Im ⟨M⟩`, CEH spectral point `x + i N^ξ η_f(x)`, CEH equation
(2.12), threshold `N^δ N^(-1/2)`).  The *target* height, loss exponent,
threshold and bad event are those of this statement at `(ξ, δ)`; the
*auxiliary* ones are at `(ξ', δ')`.  The results are:

* `regularWindow_canonicalCenter_sub_le`: on the source window
  `|x - E₀| ≤ N^(β-1)` of a regular boundary window, the centers
  `⟨Γ(x + i N^ξ η_f(x)) J⟩` and `⟨Γ(x + i N^ξ' η_f(x)) J⟩` differ by an
  explicit `O(N^(ξ-1) + N^(ξ'-1))`, through the boundary center.
* `eventually_auxiliaryLoss_scalarConditions`: for `ξ, ξ' < 1/2` and any
  smaller auxiliary loss exponent `δ' < δ`, this discrepancy plus the
  auxiliary threshold is eventually below the target threshold, with one
  cutoff uniform in `s ≥ sLo`.
* `exists_localETHWindowBad_auxiliaryLoss` and its measure and
  polynomial-tail corollaries: the target bad event at `(ξ, δ)` is
  contained in the bad event at `(ξ', δ')`, for every admissible MDE branch
  and spacing function (canonicalized by `TypicalSpacingLocalETHAssembly`).

No ETH estimate, two-resolvent law, or conditional certificate is assumed
or constructed.  The probability statements are measure monotonicity only;
the auxiliary tail bound itself is a hypothesis here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set Matrix MeasureTheory
open scoped Topology Matrix.Norms.L2Operator ComplexConjugate

/-!
### Matrix estimates for the diagonal center
-/

/-- The matrix imaginary part is a contraction for the operator norm. -/
theorem norm_localETHImPart_le {N : ℕ} (A : LocalETHMatrix N) :
    ‖localETHImPart A‖ ≤ ‖A‖ := by
  unfold localETHImPart
  rw [norm_smul]
  have h2 : ‖(2 * Complex.I)⁻¹‖ = 1 / 2 := by
    simp
  rw [h2]
  have hsub : ‖A - Aᴴ‖ ≤ ‖A‖ + ‖A‖ := by
    calc
      ‖A - Aᴴ‖ ≤ ‖A‖ + ‖Aᴴ‖ := norm_sub_le _ _
      _ = ‖A‖ + ‖A‖ := by rw [Matrix.l2_opNorm_conjTranspose]
  linarith

/-- The matrix imaginary part is additive. -/
theorem localETHImPart_sub {N : ℕ} (A B : LocalETHMatrix N) :
    localETHImPart A - localETHImPart B = localETHImPart (A - B) := by
  unfold localETHImPart
  rw [Matrix.conjTranspose_sub, ← smul_sub]
  congr 1
  abel

/-- The diagonal center is the normalized trace of `Im M J` divided by
`Im ⟨M⟩`. -/
theorem normalizedTrace_localETHGamma_mul {N : ℕ}
    (M J : LocalETHMatrix N) :
    Conventions.normalizedTrace (localETHGamma M * J) =
      (((Conventions.normalizedTrace M).im : ℂ))⁻¹ *
        Conventions.normalizedTrace (localETHImPart M * J) := by
  unfold localETHGamma
  rw [Matrix.smul_mul]
  unfold Conventions.normalizedTrace
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

/-- Lipschitz bound for the diagonal center `⟨Γ(M) J⟩` near a matrix with
imaginary trace bounded below by `c`.  The constant `2/c + 2L/c²` depends only
on the lower bound `c` and the norm bound `L` of the reference matrix. -/
theorem norm_normalizedTrace_localETHGamma_mul_sub_le
    {N : ℕ} (hN : 0 < N) {A B J : LocalETHMatrix N} {ε c L : ℝ}
    (hc : 0 < c) (hAB : ‖A - B‖ ≤ ε) (hε : ε ≤ c / 2)
    (hB : ‖B‖ ≤ L) (hBim : c ≤ (Conventions.normalizedTrace B).im)
    (hJ : ‖J‖ ≤ 1) :
    ‖Conventions.normalizedTrace (localETHGamma A * J) -
        Conventions.normalizedTrace (localETHGamma B * J)‖ ≤
      (2 / c + 2 * L / c ^ 2) * ε := by
  rw [normalizedTrace_localETHGamma_mul, normalizedTrace_localETHGamma_mul]
  set a := Conventions.normalizedTrace (localETHImPart A * J)
  set a' := Conventions.normalizedTrace (localETHImPart B * J)
  set b := (Conventions.normalizedTrace A).im
  set b' := (Conventions.normalizedTrace B).im
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hAB
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hB
  have htrsub : Conventions.normalizedTrace A - Conventions.normalizedTrace B =
      Conventions.normalizedTrace (A - B) := by
    unfold Conventions.normalizedTrace
    rw [Matrix.trace_sub]
    ring
  have hbb : |b - b'| ≤ ε := by
    have h1 : |b - b'| ≤ ‖Conventions.normalizedTrace A -
        Conventions.normalizedTrace B‖ := by
      have := Complex.abs_im_le_norm
        (Conventions.normalizedTrace A - Conventions.normalizedTrace B)
      simpa [b, b'] using this
    rw [htrsub] at h1
    exact h1.trans ((norm_normalizedTrace_le_localETHNorm hN _).trans hAB)
  have hb' : c ≤ b' := hBim
  have hb : c / 2 ≤ b := by
    have := (abs_le.mp hbb).1
    linarith
  have hbpos : 0 < b := by linarith
  have hb'pos : 0 < b' := by linarith
  have haa : ‖a - a'‖ ≤ ε := by
    have hsub : a - a' = Conventions.normalizedTrace
        (localETHImPart (A - B) * J) := by
      simp only [a, a']
      unfold Conventions.normalizedTrace
      rw [← localETHImPart_sub, Matrix.sub_mul, Matrix.trace_sub]
      ring
    rw [hsub]
    refine (norm_normalizedTrace_le_localETHNorm hN _).trans ?_
    calc
      ‖localETHImPart (A - B) * J‖ ≤ ‖localETHImPart (A - B)‖ * ‖J‖ :=
        norm_mul_le _ _
      _ ≤ ‖A - B‖ * 1 := by
        gcongr
        exact norm_localETHImPart_le _
      _ ≤ ε := by simpa using hAB
  have ha' : ‖a'‖ ≤ L := by
    refine (norm_normalizedTrace_le_localETHNorm hN _).trans ?_
    calc
      ‖localETHImPart B * J‖ ≤ ‖localETHImPart B‖ * ‖J‖ := norm_mul_le _ _
      _ ≤ ‖B‖ * 1 := by
        gcongr
        exact norm_localETHImPart_le _
      _ ≤ L := by simpa using hB
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hb'C : (b' : ℂ) ≠ 0 := by exact_mod_cast hb'pos.ne'
  have hident : (b : ℂ)⁻¹ * a - (b' : ℂ)⁻¹ * a' =
      (b : ℂ)⁻¹ * (a - a') + (b : ℂ)⁻¹ * (b' : ℂ)⁻¹ * a' * ((b' : ℂ) - b) := by
    field_simp
    ring
  rw [hident]
  have hnb : ‖(b : ℂ)⁻¹‖ = b⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hbpos.le]
  have hnb' : ‖(b' : ℂ)⁻¹‖ = b'⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hb'pos.le]
  have hdiff : ‖(b' : ℂ) - b‖ ≤ ε := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hbb
  have hbinv : b⁻¹ ≤ 2 / c := by
    rw [inv_le_comm₀ hbpos (by positivity), inv_div]
    exact hb
  have hb'inv : b'⁻¹ ≤ 1 / c := by
    rw [inv_le_comm₀ hb'pos (by positivity)]
    simpa using hb'
  calc
    ‖(b : ℂ)⁻¹ * (a - a') + (b : ℂ)⁻¹ * (b' : ℂ)⁻¹ * a' * ((b' : ℂ) - b)‖
        ≤ ‖(b : ℂ)⁻¹ * (a - a')‖ +
          ‖(b : ℂ)⁻¹ * (b' : ℂ)⁻¹ * a' * ((b' : ℂ) - b)‖ := norm_add_le _ _
    _ = b⁻¹ * ‖a - a'‖ + b⁻¹ * b'⁻¹ * ‖a'‖ * ‖(b' : ℂ) - b‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, hnb, hnb']
    _ ≤ (2 / c) * ε + (2 / c) * (1 / c) * L * ε := by
      gcongr
    _ = (2 / c + 2 * L / c ^ 2) * ε := by
      field_simp

/-!
### The center at one canonical CEH height versus the boundary
-/

/-- At positive height the unconditional Hermitian branch is the spectral lift
of the upper scalar entries. -/
theorem hermitianMDEBranch_eq_spectralLift_upper
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    hermitianMDEBranch hF hs z =
      spectralLift hF (entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z)) := by
  rw [hermitianMDEBranch, dite_eq_left hN, hermitianMDEMean_of_im_pos hF hN hs hz]

/-- Spectral transport is additive in the diagonal data. -/
theorem spectralLift_sub {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (p q : Fin N → ℂ) :
    spectralLift hF p - spectralLift hF q = spectralLift hF (p - q) := by
  unfold spectralLift
  rw [← map_sub, Matrix.diagonal_sub]
  rfl

/-- **One canonical height against the boundary.**  At a point `x` of a
regular boundary window, the center at the canonical CEH spectral
point `x + i N^ξ η_f(x)` (unconditional Hermitian branch, canonical spacing)
is within `(2/c + 2K/c²) · canonicalVerticalEntryRate N ξ s c` of the
boundary center `⟨Γ(M_s(x)) J⟩`.  The two scalar side conditions are the
explicit eventual facts of `ThetaOnePublishedAdapter`; normalization is the
normalized trace and `G ∼ GUE_N(s/N)` plays no role (deterministic). -/
theorem norm_canonicalCenter_sub_boundaryGamma_le
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s c K x ξ : ℝ} (hs : 0 < s) (hc : 0 < c) (hξ₀ : 0 ≤ ξ)
    {Mb : LocalETHMatrix N}
    (hboundary : Tendsto
      (fun η : ℝ => hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds Mb))
    (hdensity : c ≤ (Conventions.normalizedTrace Mb).im)
    (hnorm : ‖Mb‖ ≤ K)
    (hstab : c ≤ ‖1 - (s : ℂ) * Conventions.normalizedTrace (Mb * Mb)‖)
    (hlarge : 1 < (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
      (c / (2 * Real.pi)))
    (hrate : canonicalVerticalEntryRate N ξ s c ≤ c / 2)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) :
    ‖localETHCenter (hermitianMDEBranch hF hs)
          (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ x J -
        Conventions.normalizedTrace (localETHGamma Mb * J)‖ ≤
      (2 / c + 2 * K / c ^ 2) * canonicalVerticalEntryRate N ξ s c := by
  have hN0 : 0 < N := by omega
  obtain ⟨hsol, hMb, hstabId⟩ :=
    boundary_matrix_scalar_identification hF hN0 hs hc hboundary hdensity
  have hbx : Tendsto (fun t : ℝ => upperBranch hN0 (hermitianSpectrum hF) hs
      ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (Conventions.normalizedTrace Mb)) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp hboundary
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hF hN0 hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hF hN0 hs (by simpa using htpos')]
  have hstab' : c ≤ ‖stabilityDenominator (hermitianSpectrum hF) s (x : ℂ)
      (Conventions.normalizedTrace Mb)‖ := by
    rw [← hstabId]
    exact hstab
  have hentry := canonicalEntry_close_boundary_le_rate hN (hermitianSpectrum hF)
    hs hc hξ₀ hsol hdensity hstab' hbx hlarge
  have hη : 0 < (N : ℝ) ^ ξ * cehTypicalSpacing N hN (hermitianSpectrum hF) hs x :=
    mul_pos (by positivity) (cehTypicalSpacing_spec N hN (hermitianSpectrum hF) hs x).1
  have hz : 0 < ((x : ℂ) + (((N : ℝ) ^ ξ *
      cehTypicalSpacing N hN (hermitianSpectrum hF) hs x : ℝ) : ℂ) *
        Complex.I).im := by
    simpa using hη
  unfold localETHCenter localETHSpectralPoint
  rw [hermitianMDEBranch_eq_spectralLift_upper hF hN0 hs hz]
  have hrate0 : 0 ≤ canonicalVerticalEntryRate N ξ s c :=
    (norm_nonneg _).trans (hentry ⟨0, hN0⟩)
  apply norm_normalizedTrace_localETHGamma_mul_sub_le hN0 hc _ hrate hnorm
    hdensity hJ
  rw [hMb, spectralLift_sub]
  rw [norm_spectralLift]
  exact (pi_norm_le_iff_of_nonneg hrate0).2 fun i => hentry i

/-!
### Two canonical heights over a regular window
-/

/-- **Comparison of the center at two CEH heights.**  For an energy
`x` in the source window `|x - E₀| ≤ N^(β-1)` of a regular boundary window
(with `N^(β-1) < r`), the centers at the canonical spectral points
`x + i N^ξ η_f(x)` and `x + i N^ξ' η_f(x)` differ by at most
`(2/c + 2K/c²)` times the sum of the two explicit vertical rates.  The
comparison goes through the boundary center `⟨Γ(M_s(x)) J⟩`. -/
theorem regularWindow_canonicalCenter_sub_le
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s E₀ r c K β ξ ξ' x : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hξ₀ : 0 ≤ ξ) (hξ'₀ : 0 ≤ ξ')
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K)
    (hx : |x - E₀| ≤ (N : ℝ) ^ (β - 1)) (hwin : (N : ℝ) ^ (β - 1) < r)
    (hlarge : 1 < (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
      (c / (2 * Real.pi)))
    (hlarge' : 1 < (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ') *
      (c / (2 * Real.pi)))
    (hrate : canonicalVerticalEntryRate N ξ s c ≤ c / 2)
    (hrate' : canonicalVerticalEntryRate N ξ' s c ≤ c / 2)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) :
    ‖localETHCenter (hermitianMDEBranch hF hs)
          (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ x J -
        localETHCenter (hermitianMDEBranch hF hs)
          (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ' x J‖ ≤
      (2 / c + 2 * K / c ^ 2) *
        (canonicalVerticalEntryRate N ξ s c +
          canonicalVerticalEntryRate N ξ' s c) := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  have hxopen : x ∈ Ioo (E₀ - r) (E₀ + r) := by
    rw [mem_Ioo]
    rw [abs_le] at hx
    constructor <;> linarith
  obtain ⟨hb, _hd, _hd', hdens, hnorm, hstab⟩ := hdata x hxopen
  have h₁ := norm_canonicalCenter_sub_boundaryGamma_le hN hF hs hc hξ₀ hb
    hdens hnorm hstab hlarge hrate J hJ
  have h₂ := norm_canonicalCenter_sub_boundaryGamma_le hN hF hs hc hξ'₀ hb
    hdens hnorm hstab hlarge' hrate' J hJ
  set A := localETHCenter (hermitianMDEBranch hF hs)
    (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ x J
  set B := localETHCenter (hermitianMDEBranch hF hs)
    (cehTypicalSpacing N hN (hermitianSpectrum hF) hs) ξ' x J
  set C₀ := Conventions.normalizedTrace (localETHGamma (Mb x) * J)
  calc
    ‖A - B‖ ≤ ‖A - C₀‖ + ‖C₀ - B‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖A - C₀‖ + ‖B - C₀‖ := by rw [norm_sub_rev C₀ B]
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add h₁ h₂

/-- A regular boundary window for an admissible MDE branch is a regular
boundary window, with the same boundary data, for the unconditional Hermitian
branch: the two branches agree on the open upper half-plane. -/
theorem localETHRegularBoundaryWindow_canonical_of_branch
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F Mf)
    {E₀ r c K : ℝ} (h : LocalETHRegularBoundaryWindow s Mf E₀ r c K) :
    LocalETHRegularBoundaryWindow s (hermitianMDEBranch hF hs) E₀ r c K := by
  obtain ⟨Mb, Mb', hdata⟩ := h.boundary
  refine ⟨⟨Mb, Mb', fun x hx => ?_⟩⟩
  obtain ⟨hb, hrest⟩ := hdata x hx
  refine ⟨?_, hrest⟩
  apply hb.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  exact localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf
    (by simpa using ht'.ne')

/-!
### Error comparison and bad-event inclusion
-/

/-- The overlap error at height exponent `ξ` exceeds the error at `ξ'` by at
most the center discrepancy at `λ_i`; off the diagonal the two errors are
equal. -/
theorem localETHError_le_add_of_center_close
    {N : ℕ} (Mf : ℂ → LocalETHMatrix N) (etaF : ℝ → ℝ) (ξ ξ' : ℝ)
    (J : LocalETHMatrix N) (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ)
    (i j : Fin N) {ε : ℝ}
    (hclose : ‖localETHCenter Mf etaF ξ (lam i) J -
      localETHCenter Mf etaF ξ' (lam i) J‖ ≤ ε) :
    localETHError Mf etaF ξ J lam u i j ≤
      localETHError Mf etaF ξ' J lam u i j + ε := by
  unfold localETHError
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte] at hclose ⊢
    calc
      _ = ‖(star (u j) ⬝ᵥ (J *ᵥ u j) - localETHCenter Mf etaF ξ' (lam j) J) -
            (localETHCenter Mf etaF ξ (lam j) J -
              localETHCenter Mf etaF ξ' (lam j) J)‖ := by
        congr 1
        ring
      _ ≤ _ := norm_sub_le _ _
      _ ≤ _ := by gcongr
  · simp only [hij, ↓reduceIte]
    have hε : 0 ≤ ε := (norm_nonneg _).trans hclose
    linarith

/-- **Deterministic bad-event inclusion.**  If, on the source window, the
centers at the target height exponent `ξ` and the auxiliary exponent `ξ'`
differ by at most `ε`, and the auxiliary threshold plus `ε` is below the
target threshold, then a target bad sample is an auxiliary bad sample.
The eigenfamily, the pair and the window are unchanged. -/
theorem localETHWindowBad_of_center_close
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {etaF : ℝ → ℝ}
    {ξ ξ' β δ δ' E₀ ε : ℝ} {F J : LocalETHMatrix N}
    {G : HermitianMatrix (Fin N)}
    (hclose : ∀ x : ℝ, |x - E₀| ≤ (N : ℝ) ^ (β - 1) →
      ‖localETHCenter Mf etaF ξ x J - localETHCenter Mf etaF ξ' x J‖ ≤ ε)
    (hbudget : (N : ℝ) ^ δ' * (N : ℝ) ^ (-(1 / 2 : ℝ)) + ε ≤
      (N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ)))
    (hbad : LocalETHWindowBad Mf etaF ξ β δ E₀ F J G) :
    LocalETHWindowBad Mf etaF ξ' β δ' E₀ F J G := by
  obtain ⟨lam, u, hfam, i, j, hi, hj, hlt⟩ := hbad
  refine ⟨lam, u, hfam, i, j, hi, hj, ?_⟩
  have herr := localETHError_le_add_of_center_close Mf etaF ξ ξ' J lam u i j
    (hclose (lam i) hi)
  linarith

/-!
### Explicit rates and the auxiliary-loss budget
-/

/-- The dimension-free constant in the canonical vertical entry rate. -/
def canonicalVerticalRateConstant (s c : ℝ) : ℝ :=
  (2 * Real.pi / c) * (1 + 8 / (s * c ^ 3)) * (s * c / 2)⁻¹ * (s * c)⁻¹

/-- The canonical vertical entry rate is exactly a constant times `N^(ξ-1)`. -/
theorem canonicalVerticalEntryRate_eq {N : ℕ} {ξ s c : ℝ}
    (hs : 0 < s) (hc : 0 < c) :
    canonicalVerticalEntryRate N ξ s c =
      canonicalVerticalRateConstant s c * (N : ℝ) ^ (ξ - 1) := by
  simp only [canonicalVerticalEntryRate, canonicalHeightRate,
    canonicalVerticalRateConstant]
  field_simp

/-- The vertical rate constant is positive for positive variance and density
lower bound. -/
theorem canonicalVerticalRateConstant_pos {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    0 < canonicalVerticalRateConstant s c := by
  unfold canonicalVerticalRateConstant
  positivity

/-- The rate constant decreases with the variance; hence a lower variance
bound `sLo` controls every `s ≥ sLo`. -/
theorem canonicalVerticalRateConstant_le_of_le {sLo s c : ℝ}
    (hsLo : 0 < sLo) (hs : sLo ≤ s) (hc : 0 < c) :
    canonicalVerticalRateConstant s c ≤ canonicalVerticalRateConstant sLo c := by
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  unfold canonicalVerticalRateConstant
  gcongr

/-- The quantitative IFT height cutoff increases with the variance. -/
theorem quantitativeIFTHeight_le_of_le {sLo s c : ℝ}
    (hsLo : 0 < sLo) (hs : sLo ≤ s) (hc : 0 < c) :
    quantitativeIFTHeight sLo c ≤ quantitativeIFTHeight s c := by
  have hR : 0 ≤ quantitativeIFTRadius sLo c :=
    (quantitativeIFTRadius_height_spec hsLo hc).1.le
  unfold quantitativeIFTHeight
  apply min_le_min
  · gcongr
  · have hRmono : quantitativeIFTRadius sLo c ≤ quantitativeIFTRadius s c := by
      unfold quantitativeIFTRadius
      apply min_le_min le_rfl
      gcongr
    gcongr
    exact hR.trans hRmono

/-- Polynomial comparison along the integers: a strictly smaller power is
eventually below any positive multiple of a larger power. -/
theorem eventually_natCast_rpow_le_mul_rpow {a b ε : ℝ} (hab : a < b)
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ ε * (N : ℝ) ^ b := by
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (a - b)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    funext N
    simp only [Function.comp_apply]
    congr 1
    ring
  filter_upwards [hlim.eventually (Iic_mem_nhds hε), eventually_ge_atTop 1]
    with N hN h1
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  calc
    (N : ℝ) ^ a = (N : ℝ) ^ (a - b) * (N : ℝ) ^ b := by
      rw [← Real.rpow_add hNpos, sub_add_cancel]
    _ ≤ ε * (N : ℝ) ^ b := by
      gcongr

/-- **Auxiliary-loss scalar budget, uniform in `s ≥ sLo`.**  For height
exponents `ξ, ξ' < 1/2`, a target loss exponent `δ > 0`, and any smaller
auxiliary loss exponent `δ' < δ`, all sufficiently large dimensions satisfy
simultaneously: `N ≥ 4`; the source window `N^(β-1)` is inside the regular
radius; both canonical heights lie below the IFT cutoff; both vertical rates
are at most `c/2`; and the auxiliary threshold `N^δ' N^(-1/2)` plus the
center discrepancy budget is at most the target threshold
`N^δ N^(-1/2)`.  The cutoff depends only on `sLo, r, c, K, β, ξ, ξ', δ, δ'`. -/
theorem eventually_auxiliaryLoss_scalarConditions
    {sLo r c K β ξ ξ' δ δ' : ℝ} (hsLo : 0 < sLo) (hr : 0 < r) (hc : 0 < c)
    (hK : 0 < K) (hβ : β < 1) (hξ : ξ < 1 / 2) (hξ' : ξ' < 1 / 2)
    (hδ : 0 < δ) (hδ' : δ' < δ) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ (N : ℝ) ^ (β - 1) < r ∧
      ∀ s : ℝ, sLo ≤ s →
        1 < (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
          (c / (2 * Real.pi)) ∧
        1 < (N : ℝ) * (quantitativeIFTHeight s c / (N : ℝ) ^ ξ') *
          (c / (2 * Real.pi)) ∧
        canonicalVerticalEntryRate N ξ s c ≤ c / 2 ∧
        canonicalVerticalEntryRate N ξ' s c ≤ c / 2 ∧
        (N : ℝ) ^ δ' * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
            (2 / c + 2 * K / c ^ 2) *
              (canonicalVerticalEntryRate N ξ s c +
                canonicalVerticalEntryRate N ξ' s c) ≤
          (N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set κ := canonicalVerticalRateConstant sLo c with hκdef
  have hκ : 0 < κ := canonicalVerticalRateConstant_pos hsLo hc
  set L := 2 / c + 2 * K / c ^ 2 with hLdef
  have hL : 0 < L := by positivity
  set ε := 1 / (4 * (L * κ)) with hεdef
  have hε : 0 < ε := by positivity
  have hLκε : L * κ * ε = 1 / 4 := by
    rw [hεdef]
    field_simp
  have hH : 0 < quantitativeIFTHeight sLo c :=
    (quantitativeIFTRadius_height_spec hsLo hc).2.1
  filter_upwards [eventually_ge_atTop 4,
    eventually_natCast_rpow_le_mul_rpow (a := β - 1) (b := 0)
      (by linarith) (half_pos hr),
    eventually_one_lt_ceh_test_density_scale (by linarith : ξ < 1) hH hc,
    eventually_one_lt_ceh_test_density_scale (by linarith : ξ' < 1) hH hc,
    eventually_natCast_rpow_le_mul_rpow (a := ξ - 1) (b := 0)
      (by linarith) (by positivity : 0 < c / (2 * κ)),
    eventually_natCast_rpow_le_mul_rpow (a := ξ' - 1) (b := 0)
      (by linarith) (by positivity : 0 < c / (2 * κ)),
    eventually_natCast_rpow_le_mul_rpow (a := δ') (b := δ) hδ'
      (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_natCast_rpow_le_mul_rpow (a := ξ - 1) (b := δ - 1 / 2)
      (by linarith) hε,
    eventually_natCast_rpow_le_mul_rpow (a := ξ' - 1) (b := δ - 1 / 2)
      (by linarith) hε]
    with N hN4 hwin hlg hlg' hsm hsm' hA hB hB'
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_zero, mul_one] at hwin hsm hsm'
  refine ⟨hN4, by linarith, ?_⟩
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  have hQ := quantitativeIFTHeight_le_of_le hsLo hs hc
  have hκs := canonicalVerticalRateConstant_le_of_le hsLo hs hc
  have hrate : canonicalVerticalEntryRate N ξ s c ≤ κ * (N : ℝ) ^ (ξ - 1) := by
    rw [canonicalVerticalEntryRate_eq hs0 hc]
    gcongr
  have hrate' : canonicalVerticalEntryRate N ξ' s c ≤
      κ * (N : ℝ) ^ (ξ' - 1) := by
    rw [canonicalVerticalEntryRate_eq hs0 hc]
    gcongr
  have hκc : κ * (c / (2 * κ)) = c / 2 := by
    field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine lt_of_lt_of_le hlg ?_
    gcongr
  · refine lt_of_lt_of_le hlg' ?_
    gcongr
  · calc
      _ ≤ κ * (N : ℝ) ^ (ξ - 1) := hrate
      _ ≤ κ * (c / (2 * κ)) := by gcongr
      _ = c / 2 := hκc
  · calc
      _ ≤ κ * (N : ℝ) ^ (ξ' - 1) := hrate'
      _ ≤ κ * (c / (2 * κ)) := by gcongr
      _ = c / 2 := hκc
  · set P := (N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ)) with hPdef
    have hP : (N : ℝ) ^ (δ - 1 / 2) = P := by
      rw [hPdef, ← Real.rpow_add hNpos]
      ring_nf
    rw [hP] at hB hB'
    have hhalf : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have h1 : (N : ℝ) ^ δ' * (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ P / 2 := by
      calc
        _ ≤ (1 / 2 * (N : ℝ) ^ δ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = P / 2 := by rw [hPdef]; ring
    have h2 : L * (canonicalVerticalEntryRate N ξ s c +
        canonicalVerticalEntryRate N ξ' s c) ≤ P / 2 := by
      calc
        _ ≤ L * (κ * (ε * P) + κ * (ε * P)) := by
          gcongr
          · exact hrate.trans (by gcongr)
          · exact hrate'.trans (by gcongr)
        _ = 2 * (L * κ * ε) * P := by ring
        _ = P / 2 := by rw [hLκε]; ring
    linarith

/-!
### Uniform auxiliary-loss conversion of the bad event
-/

/-- **Uniform deterministic auxiliary-loss conversion.**  Fix `sLo, r, c, K`
(the variance lower bound and regular-window data), a window exponent
`β < 1`, height exponents `0 ≤ ξ, ξ' < 1/2`, a target loss exponent
`δ > 0`, and a smaller auxiliary loss exponent `δ' < δ`.  There is one cutoff
`N₀ ≥ 4`, depending only on these fixed data, such that for every `N ≥ N₀`,
every variance `s ≥ sLo`, every Hermitian deformation, every admissible MDE
branch and typical-spacing function, every regular boundary window center
`E₀` and every observable with `‖J‖ ≤ 1`, a sample that is bad for the
target event at `(ξ, δ)` is bad for the event at `(ξ', δ')`.  The event
quantifies over every orthonormal eigenfamily and every pair in the window
`N^(β-1)`, exactly as `LocalETHWindowBad`. -/
theorem exists_localETHWindowBad_auxiliaryLoss
    {sLo r c K β ξ ξ' δ δ' : ℝ} (hsLo : 0 < sLo) (hr : 0 < r) (hc : 0 < c)
    (hK : 0 < K) (hβ : β < 1) (hξ₀ : 0 ≤ ξ) (hξ : ξ < 1 / 2)
    (hξ'₀ : 0 ≤ ξ') (hξ' : ξ' < 1 / 2) (hδ : 0 < δ) (hδ' : δ' < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ s : ℝ, sLo ≤ s →
      ∀ F : HermitianMatrix (Fin N),
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, ‖J‖ ≤ 1 →
      ∀ G : HermitianMatrix (Fin N),
        LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G →
          LocalETHWindowBad Mf etaF ξ' β δ' E₀ F.1 J G := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (eventually_auxiliaryLoss_scalarConditions (K := K) hsLo hr hc hK hβ
      hξ hξ' hδ hδ')
  refine ⟨max N₀ 4, le_max_right _ _, ?_⟩
  intro N hN s hs F Mf hMf etaF hetaF E₀ hreg J hJ G hbad
  obtain ⟨hN4, hwin, hsc⟩ := hN₀ N (le_of_max_le_left hN)
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  obtain ⟨hlg, hlg', hrt, hrt', hbudget⟩ := hsc s hs
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch F.2 hs0 hMf hreg
  apply localETHWindowBad_of_center_close _ hbudget hbad
  intro x hx
  rw [localETHCenter_eq_canonicalSpacing hN4 F.2 hs0 hMf hetaF ξ x J,
    localETHCenter_eq_canonicalSpacing hN4 F.2 hs0 hMf hetaF ξ' x J]
  exact regularWindow_canonicalCenter_sub_le hN4 F.2 hs0 hc hξ₀ hξ'₀ hregC hx
    hwin hlg hlg' hrt hrt' J hJ

/-- **Probability monotonicity.**  Under the hypotheses of
`exists_localETHWindowBad_auxiliaryLoss`, for every measure on Hermitian
matrices (in particular `GUE_N(s/N)`), the target bad event at `(ξ, δ)`
has measure at most that of the auxiliary bad event at `(ξ', δ')`, with the
same uniform cutoff. -/
theorem exists_measure_localETHWindowBad_le_auxiliaryLoss
    {sLo r c K β ξ ξ' δ δ' : ℝ} (hsLo : 0 < sLo) (hr : 0 < r) (hc : 0 < c)
    (hK : 0 < K) (hβ : β < 1) (hξ₀ : 0 ≤ ξ) (hξ : ξ < 1 / 2)
    (hξ'₀ : 0 ≤ ξ') (hξ' : ξ' < 1 / 2) (hδ : 0 < δ) (hδ' : δ' < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ s : ℝ, sLo ≤ s →
      ∀ F : HermitianMatrix (Fin N),
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, ‖J‖ ≤ 1 →
      ∀ μ : Measure (HermitianMatrix (Fin N)),
        μ {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ≤
          μ {G | LocalETHWindowBad Mf etaF ξ' β δ' E₀ F.1 J G} := by
  obtain ⟨N₀, hN₀4, h⟩ := exists_localETHWindowBad_auxiliaryLoss (K := K)
    hsLo hr hc hK hβ hξ₀ hξ hξ'₀ hξ' hδ hδ'
  refine ⟨N₀, hN₀4, ?_⟩
  intro N hN s hs F Mf hMf etaF hetaF E₀ hreg J hJ μ
  exact measure_mono fun G hG =>
    h N hN s hs F Mf hMf etaF hetaF E₀ hreg J hJ G hG

/-- **Polynomial-tail transfer at the target exponents.**  Fix the
data `κ, C, sLo ≤ sHi, r, c, K`, the exact exponents
`0 < ξ < β ≤ 1/2`, a loss exponent `δ > 0` and an arbitrary polynomial tail
exponent `D`.  Let `0 ≤ ξ' ≤ ξ` and `δ' < δ` be auxiliary exponents.  If the
`GUE_N(s/N)` probability of the bad event at the auxiliary exponents
`(ξ', δ')` is eventually at most `N^(-D)`, uniformly in exactly the
quantifiers of `LocalETHRegularWindowBound`, then so is the probability of
the target bad event at `(ξ, δ)`, with the same `D`.

This is a monotonicity statement only: its hypothesis is the auxiliary tail
bound, which this module neither proves nor packages as an input. -/
theorem localETHWindowBad_polynomialTail_of_auxiliaryLoss
    (gue : LocalETHGUEFamily) {κ C sLo sHi r c K β ξ ξ' δ δ' D : ℝ}
    (hsLo : 0 < sLo) (hr : 0 < r) (hc : 0 < c) (hK : 0 < K)
    (hξ : 0 < ξ) (hξβ : ξ < β) (hβ : β ≤ 1 / 2)
    (hξ'₀ : 0 ≤ ξ') (hξ'ξ : ξ' ≤ ξ) (hδ : 0 < δ) (hδ' : δ' < δ)
    (haux : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | LocalETHWindowBad Mf etaF ξ' β δ' E₀ F.1 J G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | LocalETHWindowBad Mf etaF ξ β δ E₀ F.1 J G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hβ1 : β < 1 := lt_of_le_of_lt hβ (by norm_num)
  have hξhalf : ξ < 1 / 2 := lt_of_lt_of_le hξβ hβ
  obtain ⟨N₀, hN₀4, hmono⟩ := exists_measure_localETHWindowBad_le_auxiliaryLoss
    (K := K) hsLo hr hc hK hβ1 hξ.le hξhalf hξ'₀ (lt_of_le_of_lt hξ'ξ hξhalf)
    hδ hδ'
  obtain ⟨N₁, hN₁⟩ := haux
  refine ⟨max N₀ N₁, le_trans (by omega) (le_max_left _ _), ?_⟩
  intro N hN s hs hsHi F hFdef Mf hMf etaF hetaF E₀ hreg J hJh hJ
  exact (hmono N (le_of_max_le_left hN) s hs F Mf hMf etaF hetaF E₀ hreg J hJ
    (gue N (s / N))).trans
    (hN₁ N (le_of_max_le_right hN) s hs hsHi F hFdef Mf hMf etaF hetaF E₀ hreg
      J hJh hJ)

end CEHNative.BlockBand.CEH
