module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneFiniteStripAssembly

/-!
# Global closed-strip map and local germ gluing

The global strip map is defined without choices: it is the boundary
witness at height zero and the MDE branch at positive height.  This
module proves the local gluing lemma at the bottom edge.  A continuous lifted
germ which agrees locally with both pieces makes this single piecewise map
continuous within the closed upper strip.  Thus overlap compatibility is used
only through proved eventual equalities, never through an assumed global
joint-continuity interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- The single global closed-strip map: the boundary witness at height zero, the
positive-height branch above it. -/
def cehGlobalStripMap {N : ℕ} (Mf : ℂ → LocalETHMatrix N)
    (Mb : ℝ → LocalETHMatrix N) (p : ℝ × ℝ) : LocalETHMatrix N :=
  if p.2 = 0 then Mb p.1
  else Mf ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

@[simp] theorem cehGlobalStripMap_zero {N : ℕ}
    (Mf : ℂ → LocalETHMatrix N) (Mb : ℝ → LocalETHMatrix N) (x : ℝ) :
    cehGlobalStripMap Mf Mb (x, 0) = Mb x := by
  simp [cehGlobalStripMap]

 theorem cehGlobalStripMap_pos {N : ℕ}
    (Mf : ℂ → LocalETHMatrix N) (Mb : ℝ → LocalETHMatrix N)
    (x η : ℝ) (hη : 0 < η) :
    cehGlobalStripMap Mf Mb (x, η) =
      Mf ((x : ℂ) + (η : ℂ) * Complex.I) := by
  simp [cehGlobalStripMap, hη.ne']

/-- Local gluing at one bottom-edge point.  The hypotheses are exactly the two
local equalities proved for a lifted scalar IFT germ in the preceding modules.
The result concerns the explicit global piecewise map, not a chosen patch. -/
theorem continuousWithinAt_cehGlobalStripMap_apply_of_germ
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    {a b ηstar x : ℝ} (_hx : x ∈ Icc a b)
    {Mext : ℂ → LocalETHMatrix N} (i j : Fin N)
    (hMcont : ContinuousAt (fun z => Mext z i j) (x : ℂ))
    (hreal : (fun y : ℝ => Mext (y : ℂ)) =ᶠ[nhds x] Mb)
    (hupper : Mext =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}] Mf) :
    ContinuousWithinAt
      (fun p : ℝ × ℝ => cehGlobalStripMap Mf Mb p i j)
      (Icc a b ×ˢ Icc 0 ηstar) (x, 0) := by
  let Z : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hZ : Continuous Z := by
    unfold Z
    fun_prop
  have hrealPull : (fun p : ℝ × ℝ => Mext (p.1 : ℂ)) =ᶠ[nhds (x, 0)]
      fun p => Mb p.1 :=
    (continuous_fst.tendsto (x, 0)).eventually hreal
  have hupperFull : ∀ᶠ z in nhds (x : ℂ), 0 < z.im → Mext z = Mf z :=
    eventually_nhdsWithin_iff.mp hupper
  have hZat : Tendsto Z (nhds (x, 0)) (nhds (x : ℂ)) := by
    rw [← show Z (x, 0) = (x : ℂ) by simp [Z]]
    exact hZ.continuousAt
  have hupperPull : ∀ᶠ p in nhds (x, 0),
      0 < (Z p).im → Mext (Z p) = Mf (Z p) :=
    hZat.eventually hupperFull
  have heq : (fun p : ℝ × ℝ => cehGlobalStripMap Mf Mb p i j) =ᶠ[
      nhdsWithin (x, 0) (Icc a b ×ˢ Icc 0 ηstar)]
      fun p => Mext (Z p) i j := by
    filter_upwards [hrealPull.filter_mono nhdsWithin_le_nhds,
      hupperPull.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with p hrealp hupperp hp
    by_cases hp0 : p.2 = 0
    · simp [cehGlobalStripMap, hp0]
      rw [← hrealp]
      simp [Z, hp0]
    · have hp2 : 0 < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hp0)
      have hzim : 0 < (Z p).im := by simp [Z, hp2]
      simp [cehGlobalStripMap, hp0]
      rw [← hupperp hzim]
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Mext (Z p) i j) (x, 0) := by
    change Tendsto (fun p : ℝ × ℝ => Mext (Z p) i j) (nhds (x, 0))
      (nhds (Mext (Z (x, 0)) i j))
    rw [show Z (x, 0) = (x : ℂ) by simp [Z]]
    exact hMcont.tendsto.comp hZat
  have hrealx : Mext (x : ℂ) = Mb x := by
    show x ∈ {y : ℝ | Mext (y : ℂ) = Mb y}
    exact mem_of_mem_nhds
      (show {y : ℝ | Mext (y : ℂ) = Mb y} ∈ nhds x from hreal)
  exact hcomp.continuousWithinAt.congr_of_eventuallyEq heq
    (by simp [cehGlobalStripMap, Z, hrealx])

/-- Once bottom-edge continuity has been obtained from the proved lifted germs
at every energy (and ordinary analyticity handles positive heights), the
explicit global map feeds directly into the compact theorem. -/
theorem uniformBoundaryToStripResidual_of_globalStrip_continuous
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    {a b ηstar : ℝ} (hηstar : 0 < ηstar)
    (hcontinuous : ∀ i j : Fin N,
      ContinuousOn (fun p => cehGlobalStripMap Mf Mb p i j)
        (Icc a b ×ˢ Icc 0 ηstar)) :
    UniformBoundaryToStripResidual Mf Mb a b := by
  apply uniformBoundaryToStripResidual_of_gluedStrip hηstar
    (cehGlobalStripMap Mf Mb) hcontinuous
  · intro x hx
    simp
  · intro x hx η hη hηstar'
    exact cehGlobalStripMap_pos Mf Mb x η hη

/-- Pointwise compatible lifted germs glue the explicit global map
entrywise.  Above the bottom edge continuity is the unconditional analyticity
of the Hermitian MDE branch; at the bottom edge it is the local gluing lemma.
Thus this is a gluing result, rather than an interface which assumes a
globally continuous extension. -/
theorem continuousOn_cehGlobalStripMap_of_local_lifts
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {Mb : ℝ → LocalETHMatrix N}
    {a b ηstar : ℝ}
    (hlifts : ∀ x ∈ Icc a b, ∃ Mext : ℂ → LocalETHMatrix N,
      (∀ i j : Fin N, ContinuousAt (fun z => Mext z i j) (x : ℂ)) ∧
      ((fun y : ℝ => Mext (y : ℂ)) =ᶠ[nhds x] Mb) ∧
      (Mext =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
        hermitianMDEBranch hF hs)) :
    ∀ i j : Fin N,
      ContinuousOn
        (fun p => cehGlobalStripMap (hermitianMDEBranch hF hs) Mb p i j)
        (Icc a b ×ˢ Icc 0 ηstar) := by
  let Z : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hZ : Continuous Z := by
    unfold Z
    fun_prop
  intro i j p hp
  by_cases hp0 : p.2 = 0
  · have hpEq : p = (p.1, 0) := Prod.ext rfl hp0
    rw [hpEq]
    obtain ⟨Mext, hMext, hreal, hupper⟩ := hlifts p.1 hp.1
    exact continuousWithinAt_cehGlobalStripMap_apply_of_germ hp.1
      i j (hMext i j) hreal hupper
  · have hp2 : 0 < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hp0)
    have hzim : 0 < (Z p).im := by simp [Z, hp2]
    have hbranch : ContinuousAt
        (fun z => hermitianMDEBranch hF hs z i j) (Z p) :=
      (analyticAt_hermitianMDEBranch_apply_of_im_pos
        hF hN hs hzim i j).continuousAt
    have hcomp : ContinuousAt
        (fun q : ℝ × ℝ => hermitianMDEBranch hF hs (Z q) i j) p :=
      hbranch.comp hZ.continuousAt
    have hpos : ∀ᶠ q : ℝ × ℝ in nhds p, 0 < q.2 :=
      continuousAt_snd.tendsto (Ioi_mem_nhds hp2)
    have heq : (fun q : ℝ × ℝ =>
        cehGlobalStripMap (hermitianMDEBranch hF hs) Mb q i j) =ᶠ[nhds p]
        fun q => hermitianMDEBranch hF hs (Z q) i j := by
      filter_upwards [hpos] with q hq
      simp [cehGlobalStripMap, Z, hq.ne']
    exact (hcomp.congr_of_eventuallyEq heq).continuousWithinAt

/-- **Fixed-dimension compact-strip closure.**  On every compact interval
strictly inside a positive regular boundary window, the exact
Hermitian MDE branch converges to the boundary witness uniformly in energy as
the height tends to zero.  The cutoff extracted here is allowed to depend on
`N`; no dimension-uniform convergence rate is asserted. -/
theorem regularBoundaryWindow_fixedN_uniformBoundaryToStripResidual
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s E₀ r c K a b : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r)) :
    ∃ Mb : ℝ → LocalETHMatrix N,
      UniformBoundaryToStripResidual
        (hermitianMDEBranch hF hs) Mb a b := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  have hlifts : ∀ x ∈ Icc a b, ∃ Mext : ℂ → LocalETHMatrix N,
      (∀ i j : Fin N, ContinuousAt (fun z => Mext z i j) (x : ℂ)) ∧
      ((fun y : ℝ => Mext (y : ℂ)) =ᶠ[nhds x] Mb) ∧
      (Mext =ᶠ[nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im}]
        hermitianMDEBranch hF hs) := by
    intro x hx
    have hxopen := hinner hx
    have hidx := boundary_matrix_scalar_identification hF hN hs hc
      (hdata x hxopen).1 (hdata x hxopen).2.2.2.1
    let mR : ℝ → ℂ := fun y => Conventions.normalizedTrace (Mb y)
    have hmRcont : ContinuousAt mR x := by
      unfold mR Conventions.normalizedTrace Matrix.trace
      have hsum : ∀ t : Finset (Fin N),
          ContinuousAt (fun y : ℝ => ∑ i ∈ t, Mb y i i) x := by
        intro t
        induction t using Finset.induction_on with
        | empty => simpa using (continuousAt_const :
            ContinuousAt (fun _ : ℝ => (0 : ℂ)) x)
        | @insert i t hit iht =>
            simp only [Finset.sum_insert hit]
            exact ((hdata x hxopen).2.1 i i).continuousAt.add iht
      exact continuousAt_const.mul (by simpa using hsum Finset.univ)
    have hopen : Ioo (E₀ - r) (E₀ + r) ∈ nhds x :=
      Ioo_mem_nhds hxopen.1 hxopen.2
    have hmRsol : ∀ᶠ y : ℝ in nhds x,
        IsSolution (hermitianSpectrum hF) s (y : ℂ) (mR y) := by
      filter_upwards [hopen] with y hy
      exact (boundary_matrix_scalar_identification hF hN hs hc
        (hdata y hy).1 (hdata y hy).2.2.2.1).1
    have hnorm : c ≤ ‖stabilityDenominator (hermitianSpectrum hF) s
        (x : ℂ) (mR x)‖ := by
      rw [← hidx.2.2]
      exact (hdata x hxopen).2.2.2.2.2
    have hstab : stabilityDenominator (hermitianSpectrum hF) s
        (x : ℂ) (mR x) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le hc hnorm)
    obtain ⟨ψ, hψ, hψx, hreal, hupper⟩ :=
      exists_analytic_boundaryMDE_extension_agrees_real hN
        (hermitianSpectrum hF) hs hidx.1 hidx.1.2 hstab mR
        hmRcont rfl hmRsol
    let Mext : ℂ → LocalETHMatrix N := liftedMDEGerm hF s ψ
    have hidentified : ∀ᶠ y : ℝ in nhds x,
        Mb y = spectralLift hF
          (entry (hermitianSpectrum hF) s (y : ℂ)
            (Conventions.normalizedTrace (Mb y))) := by
      filter_upwards [hopen] with y hy
      exact (boundary_matrix_scalar_identification hF hN hs hc
        (hdata y hy).1 (hdata y hy).2.2.2.1).2.1
    have hagree := eventually_liftedMDEGerm_agrees_boundary_and_upper
      hF hN hs hreal hidentified hupper
    refine ⟨Mext, ?_, hagree.1, hagree.2⟩
    intro i j
    exact continuousAt_liftedMDEGerm_apply_at_boundary
      hF hs hψ hψx hidx.1.2 i j
  refine ⟨Mb, uniformBoundaryToStripResidual_of_globalStrip_continuous
    (show (0 : ℝ) < 1 by norm_num) ?_⟩
  exact continuousOn_cehGlobalStripMap_of_local_lifts
    hF hN hs hlifts

end CEHNative.BlockBand.CEH
