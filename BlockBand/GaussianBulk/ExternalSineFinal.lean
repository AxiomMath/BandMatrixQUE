module

public import BlockBand.GaussianBulk.ExternalSineRemainderKernel

/-!
# The external-source sine-kernel theorem

Law: `F + √t G_N`, `G_N` normalized GUE (`deformedFactorialCorrelation`), through the finite Johansson
formula (`Johansson.SourceContract`) at `S = t/N`. Uniformity, as in `ExternalSineKernelCore`: for
fixed `A, tLo ≤ tHi, v > 0, ELo, EHi, L` there are `C` and `N₀` such that for all `N ≥ N₀`,
Hermitian `F` with `‖F‖ ≤ N^A` (Euclidean operator norm), `t ∈ [tLo, tHi]`, `E ∈ [ELo, EHi]`,
every boundary MDE solution `M` with `Im⟨M⟩ ≥ v`, and `ξ, ζ ∈ [-L, L]`, the gauged rescaled kernel
is within `C N^{-1/2}` of `sinc(π(ξ-ζ))`.

Assembly of the kernel core and of `ExternalSine`: the determinantal formula
`externalSine_step1`, the scalar MDE `finiteMDE_of_boundaryMDE` and the saddle identities
(`x₀`, `levelHeight d t x₀ = t π ρ`, `levelPsi d t x₀ = E`, `η = tLo v ≤ y₀`), the residue
identity `gaugedKernel_sub_sine_eq`, the loop bound
`norm_curveIntegral_nativeGraftedLevelLoop_le` and its uniform rate
`loopRemainderBound_rate`; the loop radius `L'` comes from `exists_range_subset_ball`.
Only `‖F‖ ≤ N^A` enters, through `Σ|d_j| ≤ N‖F‖` (loop length).

Inputs: `Johansson.SourceContract` (for `externalSineKernelCore_holds`) and additionally
`PSSS.SourceContract` (for `externalSine_holds`, through `externalSine_of_core`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology Matrix
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal Matrix.Norms.L2Operator

/-- **The kernel clause of the external-source sine-kernel theorem** (the kernel core), from
`Johansson.SourceContract`. -/
theorem externalSineKernelCore_holds (hJ : Johansson.SourceContract) : ExternalSineKernelCore := by
  intro A tLo tHi v ELo EHi L htLo htle hv
  set nA := Nat.ceil |A|
  obtain ⟨C₀, N₀, hrate⟩ := loopRemainderBound_rate tLo tHi v L nA htLo htle hv
  refine ⟨C₀ / (4*Real.pi*(tLo*v)), max N₀ 1, ?_⟩
  intro N hN F hF hFn t ht E _ M hM hvM
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hN1r : (1:ℝ) ≤ N := by exact_mod_cast hNpos
  set d := spectralSource F hF with hd
  set m := CEH.normalizedTrace M with hmdef
  have hMDE := (finiteMDE_of_boundaryMDE F hF t E M hM).1
  have htpos : (0:ℝ) < t := lt_of_lt_of_le htLo ht.1
  have htpos' : 0 < t := htpos
  have hm : 0 < m.im := lt_of_lt_of_le hv hvM
  set x₀ := (saddlePoint E t m).re with hx₀
  set η := tLo * v with hηdef
  have hη : 0 < η := mul_pos htLo hv
  have hheight : η ≤ levelHeight d t x₀ :=
    actualLevelGraphPoint_MDE_bulk_height hNpos d E t tLo v m htLo ht.1 hv hvM hMDE
  have hpsi : levelPsi d t x₀ = E := levelPsi_at_saddle hNpos d E t m htpos hm hMDE
  set ρ := m.im / Real.pi with hρdef
  have hρ : 0 < ρ := div_pos hm Real.pi_pos
  have hρv : v / Real.pi ≤ ρ := div_le_div_of_nonneg_right hvM Real.pi_pos.le
  have hy : levelHeight d t x₀ = t * Real.pi * ρ := by
    rw [hx₀, levelHeight_at_saddle hNpos d E t m htpos hm hMDE, hρdef]
    simp only [saddlePoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_add, zero_mul, add_zero]
    field_simp
  obtain ⟨hC, hcont, hcorr⟩ := externalSine_step1 hJ hNpos t htpos' F hF
  refine ⟨Johansson.kernel (Johansson.sourceTime N t) d (∑ j, |d j| + 1) (∑ j, |d j| + 1 + 1),
    fun ξ => realSineGauge N E t ρ x₀ ξ, hcont, hcorr, ?_⟩
  intro ξ hξ ζ hζ
  -- the loop and its radius
  obtain ⟨ρ', hρ'⟩ := exists_range_subset_ball (nativeGraftedLevelLoop hNpos d t tHi η x₀ htpos)
  set L' := max (∑ j, |d j| + 1 + 1) ρ' with hL'
  have hball : range (nativeGraftedLevelLoop hNpos d t tHi η x₀ htpos) ⊆ Metric.ball 0 L' :=
    hρ'.trans (Metric.ball_subset_ball (le_max_right _ _))
  have heq := gaugedKernel_sub_sine_eq hNpos d _ _ hC E ρ ξ ζ t htpos' hρ tHi η x₀ ht.2 hη
    hheight hy L' (le_max_left _ _) hball
  -- the rate
  have hxi : |ξ| ≤ L := abs_le.mpr ⟨by linarith [hξ.1], hξ.2⟩
  have hdR : graftedDeformationRadius d ≤ (N:ℝ)^(nA+1) := by
    have h1 := graftedDeformationRadius_spectralSource_le F hF
    have h2 : (N:ℝ)^A ≤ (N:ℝ)^nA := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hN1r ((le_abs_self A).trans (Nat.le_ceil _))
    rw [pow_succ]
    calc graftedDeformationRadius d ≤ N * ‖F‖ := h1
      _ ≤ N * (N:ℝ)^nA := mul_le_mul_of_nonneg_left (hFn.trans h2) (by positivity)
      _ = (N:ℝ)^nA * N := by ring
  obtain ⟨-, hscale, hloopB⟩ := hrate N hN₀ d t ρ ξ ht hρv hxi hdR
  -- the loop bound
  have hS : 0 < Johansson.sourceTime N t := by
    rw [Johansson.sourceTime]; exact div_pos htpos' (by exact_mod_cast hNpos)
  set K : Set ℂ := {z | z.re < L' ∧ ∀ j, z ≠ (d j : ℂ)} with hK
  have hKstar : ∀ z ∈ K, star z ∈ K := by
    intro z hz
    refine ⟨by simpa using hz.1, fun j h => hz.2 j ?_⟩
    have := congrArg star h
    simpa using this
  have hKr : range (nativeGraftedLevelLoop hNpos d t tHi η x₀ htpos) ⊆ K := by
    intro z hz
    refine ⟨?_, fun j => nativeGraftedLevelLoop_ne_pole hNpos d t tHi η x₀ htpos ht.2 hη hheight
      j z hz⟩
    have h1 := hball hz
    rw [Metric.mem_ball, dist_zero_right] at h1
    exact lt_of_le_of_lt (Complex.re_le_norm z) h1
  have hloop := norm_curveIntegral_nativeGraftedLevelLoop_le hNpos d E t tHi η ρ x₀ ξ ζ htpos ht.2
    hη hheight hρ hpsi hscale _ K (pieceIntegrable_gaugedRemainder _ hS d _ _ L' x₀ _) hKstar hKr
    (fun z hz hre => norm_gauge_mul_remainderIntegrand_le hNpos d E ρ x₀ ξ ζ L' t htpos' hρ z hre
      (hKr hz).1 (hKr hz).2)
  -- conclude
  have hcast : ((((N:ℝ)*ρ : ℝ)) : ℂ) = ((N:ℝ):ℂ) * ((m.im : ℂ) / (Real.pi : ℂ)) := by
    rw [hρdef]; push_cast; ring
  simp only at heq ⊢
  rw [← hcast, heq, norm_div, norm_mul, norm_pow, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ t*ρ)]
  have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hden : 4*Real.pi*(tLo*v) ≤ (2*Real.pi*1)^2*(t*ρ) := by
    have h3 : tLo*v/Real.pi ≤ t*ρ := by
      rw [mul_div_assoc]; exact mul_le_mul ht.1 hρv (by positivity) htpos.le
    have h4 : (2*Real.pi*1)^2*(tLo*v/Real.pi) = 4*Real.pi*(tLo*v) := by
      field_simp
      norm_num
    rw [← h4]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hnum : 0 ≤ C₀ * (N:ℝ)^(-(1:ℝ)/2) := (norm_nonneg _).trans (hloop.trans hloopB)
  calc ‖curveIntegral _ _‖ / ((2*Real.pi*1)^2*(t*ρ))
      ≤ C₀ * (N:ℝ)^(-(1:ℝ)/2) / ((2*Real.pi*1)^2*(t*ρ)) :=
        div_le_div_of_nonneg_right (hloop.trans hloopB) (by positivity)
    _ ≤ C₀ * (N:ℝ)^(-(1:ℝ)/2) / (4*Real.pi*(tLo*v)) :=
        div_le_div_of_nonneg_left hnum (by positivity) hden
    _ = C₀ / (4*Real.pi*(tLo*v)) * (N:ℝ)^(-(1:ℝ)/2) := by ring

/-- **The external-source sine-kernel theorem `ExternalSine`** (all three clauses) from
Johansson's finite formula and the PSSS factorial-count theorem. -/
theorem externalSine_holds (hJ : Johansson.SourceContract) (source : PSSS.SourceContract.{0}) :
    ExternalSine :=
  externalSine_of_core source (externalSineKernelCore_holds hJ)

end BlockBand.GaussianBulk
