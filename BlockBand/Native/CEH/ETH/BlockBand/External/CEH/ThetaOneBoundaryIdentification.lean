module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneHolomorphicExtension

/-!
# Identification of the CEH matrix boundary witness

This module passes the exact finite matrix Dyson inverse equation through the
pointwise positive-height boundary limit.  It identifies the boundary matrix
with the spectral lift at its normalized trace, proves that trace is a
real-boundary scalar MDE solution, and transfers the matrix stability
expression to the exact scalar stability denominator.

The argument uses only `LocalETHRegularBoundaryWindow.boundary`, positivity of
its density margin, and continuity of finite-dimensional matrix operations.
No boundary identification or joint energy-height continuity is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set Matrix
open scoped Topology

/-- The matrix inverse equation survives a pointwise vertical boundary limit. -/
theorem boundary_matrix_inverse_equation
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {x : ℝ} {Mb : LocalETHMatrix N}
    (hboundary : Tendsto
      (fun η : ℝ => hermitianMDEBranch hF hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds Mb)) :
    (F - ((x : ℂ) + (s : ℂ) * Conventions.normalizedTrace Mb) •
        (1 : LocalETHMatrix N)) * Mb = 1 := by
  let l : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) l (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hz : Tendsto
      (fun η : ℝ => (x : ℂ) + (η : ℂ) * Complex.I) l (nhds (x : ℂ)) := by
    simpa using tendsto_const_nhds.add (hη.mul tendsto_const_nhds)
  let G : ℂ × LocalETHMatrix N → LocalETHMatrix N := fun p =>
    (F - (p.1 + (s : ℂ) * Conventions.normalizedTrace p.2) •
      (1 : LocalETHMatrix N)) * p.2
  have hG : Continuous G := by
    unfold G
    have ht : Continuous (fun p : ℂ × LocalETHMatrix N =>
        Conventions.normalizedTrace p.2) :=
      continuous_normalizedTrace.comp continuous_snd
    have hscalar : Continuous (fun p : ℂ × LocalETHMatrix N =>
        p.1 + (s : ℂ) * Conventions.normalizedTrace p.2) :=
      continuous_fst.add (continuous_const.mul ht)
    exact (continuous_const.sub (hscalar.smul continuous_const)).mul continuous_snd
  have hlim : Tendsto (fun η : ℝ => G
      ((x : ℂ) + (η : ℂ) * Complex.I,
        hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I)))
      l (nhds (G ((x : ℂ), Mb))) :=
    hG.continuousAt.tendsto.comp (hz.prodMk_nhds hboundary)
  have heq : (fun η : ℝ => G
      ((x : ℂ) + (η : ℂ) * Complex.I,
        hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I))) =ᶠ[l]
      fun _ => (1 : LocalETHMatrix N) := by
    filter_upwards [self_mem_nhdsWithin] with η hηpos
    apply hermitianMDEBranch_inv hF hN hs
    have hηne : η ≠ 0 := ne_of_gt hηpos
    simpa using hηne
  have hone : Tendsto (fun _ : ℝ => (1 : LocalETHMatrix N)) l (nhds 1) :=
    tendsto_const_nhds
  have hlimone : Tendsto (fun η : ℝ => G
      ((x : ℂ) + (η : ℂ) * Complex.I,
        hermitianMDEBranch hF hs ((x : ℂ) + (η : ℂ) * Complex.I)))
      l (nhds 1) := hone.congr' heq.symm
  have : G ((x : ℂ), Mb) = 1 := tendsto_nhds_unique hlim hlimone
  exact this

/-- Complete scalar/matrix identification at one regular real-boundary point. -/
theorem boundary_matrix_scalar_identification
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) {x : ℝ}
    {Mb : LocalETHMatrix N}
    (hboundary : Tendsto
      (fun η : ℝ => hermitianMDEBranch hF hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds Mb))
    (hdensity : c ≤ (Conventions.normalizedTrace Mb).im) :
    let m := Conventions.normalizedTrace Mb
    IsSolution (hermitianSpectrum hF) s (x : ℂ) m ∧
    Mb = spectralLift hF (entry (hermitianSpectrum hF) s (x : ℂ) m) ∧
    1 - (s : ℂ) * Conventions.normalizedTrace (Mb * Mb) =
      stabilityDenominator (hermitianSpectrum hF) s (x : ℂ) m := by
  let m := Conventions.normalizedTrace Mb
  have hmim : 0 < m.im := lt_of_lt_of_le hc hdensity
  have hh : effectiveHeight s (x : ℂ) m ≠ 0 := by
    have : 0 < effectiveHeight s (x : ℂ) m := by
      simpa [effectiveHeight] using mul_pos hs hmim
    exact this.ne'
  have hinv := boundary_matrix_inverse_equation hF hN hs hboundary
  have hspectral : Mb = spectralLift hF
      (entry (hermitianSpectrum hF) s (x : ℂ) m) := by
    exact Matrix.right_inv_eq_right_inv hinv
      (spectralLift_entry_inverse hF s (x : ℂ) m hh)
  have hmfixed : m = average
      (entry (hermitianSpectrum hF) s (x : ℂ) m) := by
    calc
      m = Conventions.normalizedTrace Mb := rfl
      _ = Conventions.normalizedTrace (spectralLift hF
          (entry (hermitianSpectrum hF) s (x : ℂ) m)) :=
        congrArg Conventions.normalizedTrace hspectral
      _ = average (entry (hermitianSpectrum hF) s (x : ℂ) m) :=
        normalizedTrace_spectralLift hF _
  have hsol : IsSolution (hermitianSpectrum hF) s (x : ℂ) m :=
    ⟨hmfixed, hmim⟩
  refine ⟨hsol, hspectral, ?_⟩
  calc
    1 - (s : ℂ) * Conventions.normalizedTrace (Mb * Mb) =
        1 - (s : ℂ) * Conventions.normalizedTrace
          (spectralLift hF (entry (hermitianSpectrum hF) s (x : ℂ) m) *
           spectralLift hF (entry (hermitianSpectrum hF) s (x : ℂ) m)) := by
      rw [← hspectral]
    _ = 1 - (s : ℂ) * average (fun i =>
        entry (hermitianSpectrum hF) s (x : ℂ) m i *
        entry (hermitianSpectrum hF) s (x : ℂ) m i) := by
      rw [normalizedTrace_spectralLift_mul]
    _ = stabilityDenominator (hermitianSpectrum hF) s (x : ℂ) m := by
      simp [stabilityDenominator, pow_two]

/-- The witness supplied by a regular boundary window is pointwise the
spectral lift of a scalar real-boundary MDE solution, with exactly the
same stability denominator. -/
theorem regularBoundaryWindow_identification
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s E₀ r c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K) :
    ∃ Mb Mb' : ℝ → LocalETHMatrix N,
      ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
        Tendsto
          (fun η : ℝ => hermitianMDEBranch hF hs
            ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)) ∧
        HasLocalETHMatrixDerivAt Mb (Mb' x) x ∧
        IsSolution (hermitianSpectrum hF) s (x : ℂ)
          (Conventions.normalizedTrace (Mb x)) ∧
        Mb x = spectralLift hF (entry (hermitianSpectrum hF) s (x : ℂ)
          (Conventions.normalizedTrace (Mb x))) ∧
        1 - (s : ℂ) * Conventions.normalizedTrace (Mb x * Mb x) =
          stabilityDenominator (hermitianSpectrum hF) s (x : ℂ)
            (Conventions.normalizedTrace (Mb x)) := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  refine ⟨Mb, Mb', ?_⟩
  intro x hx
  have hid := boundary_matrix_scalar_identification hF hN hs hc
    (hdata x hx).1 (hdata x hx).2.2.2.1
  exact ⟨(hdata x hx).1, (hdata x hx).2.1, hid.1, hid.2.1, hid.2.2⟩

/-- Every point of a positive regular boundary window carries the
holomorphic scalar germ from the implicit-function theorem, identified with
the unconditional upper branch on its upper-half-plane side. -/
theorem regularBoundaryWindow_analytic_scalar_germs
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s E₀ r c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K) :
    ∃ Mb Mb' : ℝ → LocalETHMatrix N,
      ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
        Tendsto
          (fun η : ℝ => hermitianMDEBranch hF hs
            ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)) ∧
        HasLocalETHMatrixDerivAt Mb (Mb' x) x ∧
        ∃ ψ : ℂ → ℂ,
          AnalyticAt ℂ ψ (x : ℂ) ∧
          ψ (x : ℂ) = Conventions.normalizedTrace (Mb x) ∧
          (ψ =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
            upperBranch hN (hermitianSpectrum hF) hs) := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  refine ⟨Mb, Mb', ?_⟩
  intro x hx
  have hid := boundary_matrix_scalar_identification hF hN hs hc
    (hdata x hx).1 (hdata x hx).2.2.2.1
  let m := Conventions.normalizedTrace (Mb x)
  have hnorm : c ≤ ‖stabilityDenominator (hermitianSpectrum hF) s
      (x : ℂ) m‖ := by
    rw [← hid.2.2]
    exact (hdata x hx).2.2.2.2.2
  have hstab : stabilityDenominator (hermitianSpectrum hF) s
      (x : ℂ) m ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le hc hnorm)
  obtain ⟨ψ, hψ, hself, _hres, heq⟩ :=
    exists_analytic_boundaryMDE_extension hN (hermitianSpectrum hF) hs
      hid.1 hid.1.2 hstab
  exact ⟨(hdata x hx).1, (hdata x hx).2.1,
    ψ, hψ, hself, heq⟩

end CEHNative.BlockBand.CEH
