module
public import BlockBand.Diffusion.Duality.BaseFin
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A Lyapunov function for the edges of the strip

In `Fin 2` coordinates, with the open strip
`openStripFin = {0 < y₀, 0 < y₁ < 1}`:
* the scale functions `log(x/(1+x))` and `log(y/(1−y))` are `𝒟₀`-harmonic in their coordinate
  (`(x(1+x)s')' = 0`, `(y(1−y)s')' = 0`); we use
  `stripLyap y = [log(1+y₀) − log y₀] + [−log y₁ − log(1−y₁)]`, whose `x`-part is minus the
  `x`-scale function (harmonic) and whose `y`-part `−log(y(1−y))` has
  `𝒟₀ = (D₀/2)(y(1−y)·(2y−1)/(y(1−y)))' = D₀`;
* `stripLyap ≥ 0` on the open strip, `stripLyap` is `C^∞` there, and on the boundary of the box
  `stripBox m = (1/m, m) × (1/m, 1 − 1/m)` away from the far edge `y₀ = m`, `stripLyap ≥ log m`.
-/

namespace BlockBand.Diffusion
open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic

/-!
### A separable generator computation
-/

/-- `mpGenerator` of `G(y₀) + H(y₁)` in `ℝ²`. -/
theorem mpGenerator_sep (b : (Fin 2 → ℝ) → Fin 2 → ℝ) (a : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    {G H G1 G2 H1 H2 : ℝ → ℝ} {y : Fin 2 → ℝ}
    (hG : ∀ᶠ x in 𝓝 (y 0), HasDerivAt G (G1 x) x) (hG1 : HasDerivAt G1 (G2 (y 0)) (y 0))
    (hH : ∀ᶠ x in 𝓝 (y 1), HasDerivAt H (H1 x) x) (hH1 : HasDerivAt H1 (H2 (y 1)) (y 1)) :
    mpGenerator b a (fun w => G (w 0) + H (w 1)) y = b y 0 * G1 (y 0) + b y 1 * H1 (y 1) +
      1 / 2 * (a y 0 0 * G2 (y 0) + a y 1 1 * H2 (y 1)) := by
  set p0 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0
  set p1 := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1
  have hap : ∀ (i : Fin 2) (w : Fin 2 → ℝ), HasFDerivAt (fun w : Fin 2 → ℝ => w i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) w := fun i w =>
    hasFDerivAt_apply i w
  have hG' : ∀ᶠ w in 𝓝 y, HasDerivAt G (G1 (w 0)) (w 0) :=
    ((continuous_apply 0).tendsto y).eventually hG
  have hH' : ∀ᶠ w in 𝓝 y, HasDerivAt H (H1 (w 1)) (w 1) :=
    ((continuous_apply 1).tendsto y).eventually hH
  have hD : ∀ᶠ w in 𝓝 y, HasFDerivAt (fun w : Fin 2 → ℝ => G (w 0) + H (w 1))
      (G1 (w 0) • p0 + H1 (w 1) • p1) w := by
    filter_upwards [hG', hH'] with w h1 h2
    exact (h1.comp_hasFDerivAt w (hap 0 w)).add (h2.comp_hasFDerivAt w (hap 1 w))
  have hT0 : HasFDerivAt (fun w : Fin 2 → ℝ => G1 (w 0)) (G2 (y 0) • p0) y :=
    hG1.comp_hasFDerivAt y (hap 0 y)
  have hT1 : HasFDerivAt (fun w : Fin 2 → ℝ => H1 (w 1)) (H2 (y 1) • p1) y :=
    hH1.comp_hasFDerivAt y (hap 1 y)
  have hF := (hT0.smul_const p0).add (hT1.smul_const p1)
  have hfd : fderiv ℝ (fun w : Fin 2 → ℝ => G (w 0) + H (w 1)) =ᶠ[𝓝 y]
      fun w => G1 (w 0) • p0 + H1 (w 1) • p1 := hD.mono fun w h => h.fderiv
  have h1 := hfd.self_of_nhds
  have h2 := hfd.fderiv_eq.trans hF.fderiv
  simp only [mpGenerator, Fin.sum_univ_two, h1, h2]
  simp [p0, p1]

/-!
### The Lyapunov function
-/

/-- The open strip in `Fin 2` coordinates. -/
def openStripFin : Set (Fin 2 → ℝ) := {y | 0 < y 0 ∧ 0 < y 1 ∧ y 1 < 1}

/-- `log(1+x) − log x = −log(x/(1+x))`. -/
def stripLyapX (x : ℝ) : ℝ := Real.log (1 + x) - Real.log x

/-- `−log y − log(1−y)`. -/
def stripLyapY (y : ℝ) : ℝ := -Real.log y - Real.log (1 - y)

/-- The Lyapunov function `stripLyapX y₀ + stripLyapY y₁`. -/
def stripLyap (y : Fin 2 → ℝ) : ℝ := stripLyapX (y 0) + stripLyapY (y 1)

theorem isOpen_openStripFin : IsOpen openStripFin :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt (continuous_apply 1) continuous_const))

theorem hasDerivAt_lyapX {x : ℝ} (hx : 0 < x) :
    HasDerivAt stripLyapX (1 / (1 + x) - 1 / x) x := by
  have h1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + x)) x := by
    have := ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
    simpa using this
  have h2 : HasDerivAt Real.log (1 / x) x := by simpa using Real.hasDerivAt_log hx.ne'
  exact h1.sub h2

theorem hasDerivAt_lyapX' {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => 1 / (1 + x) - 1 / x) (-1 / (1 + x) ^ 2 + 1 / x ^ 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 / (1 + x)) (-1 / (1 + x) ^ 2) x := by
    have h := ((hasDerivAt_id x).const_add 1).inv (show 1 + id x ≠ 0 by simp; linarith)
    convert h using 1
    · funext y; simp [one_div]
    · simp
  have h2 : HasDerivAt (fun x : ℝ => 1 / x) (-1 / x ^ 2) x := by
    have h := hasDerivAt_inv hx.ne'
    convert h using 1
    · funext y; simp [one_div]
    · ring
  convert h1.sub h2 using 1
  ring

theorem hasDerivAt_lyapY {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    HasDerivAt stripLyapY (-(1 / y) + 1 / (1 - y)) y := by
  have h1 : HasDerivAt Real.log (1 / y) y := by simpa using Real.hasDerivAt_log hy.ne'
  have h2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - y)) y := by
    have := ((hasDerivAt_id y).const_sub 1).log (by simp; linarith)
    simpa using this
  convert h1.neg.sub h2 using 1
  · funext z; simp [stripLyapY]
  · ring

theorem hasDerivAt_lyapY' {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun y => -(1 / y) + 1 / (1 - y)) (1 / y ^ 2 + 1 / (1 - y) ^ 2) y := by
  have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-1 / y ^ 2) y := by
    have h := hasDerivAt_inv hy.ne'
    convert h using 1
    · funext z; simp [one_div]
    · ring
  have h2 : HasDerivAt (fun x : ℝ => 1 / (1 - x)) (1 / (1 - y) ^ 2) y := by
    have h := ((hasDerivAt_id y).const_sub 1).inv (show 1 - id y ≠ 0 by simp; linarith)
    convert h using 1
    · funext z; simp [one_div]
    · simp
  convert h1.neg.add h2 using 1
  ring

/-- **`𝒟₀ stripLyap = D₀` on the open strip.** -/
theorem mpGenerator_baseDrift_lyap (D0 : ℝ) {y : Fin 2 → ℝ} (hy : y ∈ openStripFin) :
    mpGenerator (baseDrift D0) (baseCov D0) stripLyap y = D0 := by
  obtain ⟨h0, h1, h2⟩ := hy
  have hG : ∀ᶠ x in 𝓝 (y 0), HasDerivAt stripLyapX (1 / (1 + x) - 1 / x) x := by
    filter_upwards [Ioi_mem_nhds h0] with x hx using hasDerivAt_lyapX hx
  have hH : ∀ᶠ x in 𝓝 (y 1), HasDerivAt stripLyapY (-(1 / x) + 1 / (1 - x)) x := by
    filter_upwards [Ioo_mem_nhds h1 h2] with x hx using hasDerivAt_lyapY hx.1 hx.2
  have e := mpGenerator_sep (baseDrift D0) (baseCov D0)
    (G2 := fun x => -1 / (1 + x) ^ 2 + 1 / x ^ 2) (H2 := fun x => 1 / x ^ 2 + 1 / (1 - x) ^ 2)
    hG (hasDerivAt_lyapX' h0) hH (hasDerivAt_lyapY' h1 h2)
  have hl : stripLyap = fun w => stripLyapX (w 0) + stripLyapY (w 1) := rfl
  rw [hl, e]
  simp only [baseDrift, baseCov]
  simp
  have h3 : (1 : ℝ) - y 1 ≠ 0 := by linarith
  have h4 : (1 : ℝ) + y 0 ≠ 0 := by linarith
  field_simp
  ring

theorem contDiffAt_lyap {y : Fin 2 → ℝ} (hy : y ∈ openStripFin) :
    ContDiffAt ℝ (⊤ : ℕ∞) stripLyap y := by
  obtain ⟨h0, h1, h2⟩ := hy
  have c0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin 2 → ℝ => w 0) y := (contDiff_apply ℝ ℝ 0).contDiffAt
  have c1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin 2 → ℝ => w 1) y := (contDiff_apply ℝ ℝ 1).contDiffAt
  have l1 := (Real.contDiffAt_log.2 (show 1 + y 0 ≠ 0 by linarith)).comp y (contDiffAt_const.add c0)
  have l2 := (Real.contDiffAt_log.2 (show y 0 ≠ 0 by linarith)).comp y c0
  have l3 := (Real.contDiffAt_log.2 (show y 1 ≠ 0 by linarith)).comp y c1
  have l4 := (Real.contDiffAt_log.2 (show 1 - y 1 ≠ 0 by linarith)).comp y (contDiffAt_const.sub c1)
  exact (l1.sub l2).add (l3.neg.sub l4)

theorem continuousOn_lyap : ContinuousOn stripLyap openStripFin := fun _ hy =>
  (contDiffAt_lyap hy).continuousAt.continuousWithinAt

theorem lyapX_pos {x : ℝ} (hx : 0 < x) : 0 < stripLyapX x := by
  unfold stripLyapX
  have := Real.log_lt_log hx (show x < 1 + x by linarith)
  linarith

theorem neg_log_le_lyapX {x : ℝ} (hx : 0 < x) : -Real.log x ≤ stripLyapX x := by
  unfold stripLyapX
  have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + x by linarith)
  linarith

theorem lyapY_ge {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    -Real.log y ≤ stripLyapY y ∧ -Real.log (1 - y) ≤ stripLyapY y := by
  unfold stripLyapY
  have a := Real.log_nonpos hy.le hy1.le
  have b := Real.log_nonpos (show (0 : ℝ) ≤ 1 - y by linarith) (show 1 - y ≤ 1 by linarith)
  constructor <;> linarith

theorem lyap_nonneg {y : Fin 2 → ℝ} (hy : y ∈ openStripFin) : 0 ≤ stripLyap y := by
  have h1 := lyapX_pos hy.1
  have h2 := (lyapY_ge hy.2.1 hy.2.2).1
  have h3 := Real.log_nonpos hy.2.1.le hy.2.2.le
  unfold stripLyap; linarith

/-!
### Boxes
-/

/-- `(1/m, m) × (1/m, 1 − 1/m)`. -/
def stripBox (m : ℕ) : Set (Fin 2 → ℝ) :=
  {y | 1 / (m : ℝ) < y 0 ∧ y 0 < m ∧ 1 / (m : ℝ) < y 1 ∧ y 1 < 1 - 1 / (m : ℝ)}

/-- `[1/m, m] × [1/m, 1 − 1/m]`. -/
def stripCBox (m : ℕ) : Set (Fin 2 → ℝ) :=
  {y | 1 / (m : ℝ) ≤ y 0 ∧ y 0 ≤ m ∧ 1 / (m : ℝ) ≤ y 1 ∧ y 1 ≤ 1 - 1 / (m : ℝ)}

theorem isOpen_box (m : ℕ) : IsOpen (stripBox m) :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 1) continuous_const)))

theorem isClosed_cbox (m : ℕ) : IsClosed (stripCBox m) :=
  (isClosed_le continuous_const (continuous_apply 0)).inter
    ((isClosed_le (continuous_apply 0) continuous_const).inter
      ((isClosed_le continuous_const (continuous_apply 1)).inter
        (isClosed_le (continuous_apply 1) continuous_const)))

theorem closure_box_subset (m : ℕ) : closure (stripBox m) ⊆ stripCBox m :=
  closure_minimal (fun _ hy => ⟨hy.1.le, hy.2.1.le, hy.2.2.1.le, hy.2.2.2.le⟩) (isClosed_cbox m)

theorem cbox_subset_openStripFin {m : ℕ} (hm : 1 ≤ m) : stripCBox m ⊆ openStripFin := by
  intro y hy
  have hm' : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  exact ⟨lt_of_lt_of_le hm' hy.1, lt_of_lt_of_le hm' hy.2.2.1, by linarith [hy.2.2.2]⟩

theorem isCompact_cbox {m : ℕ} (hm : 1 ≤ m) : IsCompact (stripCBox m) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_cbox m) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := m)).subset fun y hy => ?_
  have hpos := cbox_subset_openStripFin hm hy
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_of_pos hpos.1]; exact hy.2.1
  · rw [Real.norm_eq_abs, abs_of_pos hpos.2.1]; linarith [hpos.2.2]

theorem isInteriorDomain_box {m : ℕ} (hm : 1 ≤ m) : IsInteriorDomain (stripBox m) openStripFin :=
  ⟨isOpen_box m, (isCompact_cbox hm).of_isClosed_subset isClosed_closure (closure_box_subset m),
    (closure_box_subset m).trans (cbox_subset_openStripFin hm)⟩

theorem box_mono {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : stripBox n ⊆ stripBox m := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h : 1 / (m : ℝ) ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le (by positivity) hnm'
  intro y hy
  exact ⟨lt_of_le_of_lt h hy.1, lt_of_lt_of_le hy.2.1 hnm', lt_of_le_of_lt h hy.2.2.1,
    by linarith [hy.2.2.2]⟩

theorem exists_box {y : Fin 2 → ℝ} (hy : y ∈ openStripFin) : ∃ n : ℕ, 1 ≤ n ∧ y ∈ stripBox n := by
  obtain ⟨h0, h1, h2⟩ := hy
  set M := max (max (1 / y 0) (y 0)) (max (1 / y 1) (1 / (1 - y 1))) with hM
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  have hMn : M < n := (lt_add_one M).trans hn
  have hM0 : 0 ≤ M := le_max_of_le_left (le_max_of_le_right h0.le)
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have a1 : 1 / y 0 < n := lt_of_le_of_lt (le_max_of_le_left (le_max_left _ _)) hMn
  have a2 : y 0 < n := lt_of_le_of_lt (le_max_of_le_left (le_max_right _ _)) hMn
  have a3 : 1 / y 1 < n := lt_of_le_of_lt (le_max_of_le_right (le_max_left _ _)) hMn
  have a4 : 1 / (1 - y 1) < n := lt_of_le_of_lt (le_max_of_le_right (le_max_right _ _)) hMn
  have h3 : 0 < 1 - y 1 := by linarith
  refine ⟨n, by exact_mod_cast hn1, ?_, a2, ?_, ?_⟩
  · rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ h0] at a1; linarith
  · rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ h1] at a3; linarith
  · have : 1 / (n : ℝ) < 1 - y 1 := by
      rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ h3] at a4; linarith
    linarith

/-- On the boundary of `stripBox m`, away from the far edge `y₀ = m`, `stripLyap ≥ log m`. -/
theorem log_le_lyap_of_boundary {m : ℕ} (hm : 1 ≤ m) {y : Fin 2 → ℝ} (hc : y ∈ stripCBox m)
    (hb : y ∉ stripBox m) (hfar : y 0 < m) : Real.log m ≤ stripLyap y := by
  have hy := cbox_subset_openStripFin hm hc
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log (1 / (m : ℝ)) = -Real.log m := by
    rw [one_div, Real.log_inv]
  have hX := lyapX_pos hy.1
  have hX' := neg_log_le_lyapX hy.1
  have hY := lyapY_ge hy.2.1 hy.2.2
  have hY0 := Real.log_nonpos hy.2.1.le hy.2.2.le
  have hY1 := Real.log_nonpos (show (0 : ℝ) ≤ 1 - y 1 by linarith [hy.2.2])
    (show 1 - y 1 ≤ 1 by linarith [hy.2.1])
  unfold stripLyap
  simp only [stripBox, mem_ofPred_eq, not_and_or, not_lt] at hb
  rcases hb with h | h | h | h
  · have := Real.log_le_log hy.1 h
    linarith
  · linarith
  · have := Real.log_le_log hy.2.1 h
    unfold stripLyapY at hY ⊢
    linarith
  · have h' : 1 - y 1 ≤ 1 / (m : ℝ) := by linarith
    have := Real.log_le_log (by linarith [hy.2.2]) h'
    unfold stripLyapY at hY ⊢
    linarith

theorem exists_bound_lyap {m : ℕ} (hm : 1 ≤ m) :
    ∃ K, 0 ≤ K ∧ ∀ y ∈ stripCBox m, stripLyap y ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_cbox hm).exists_bound_of_continuousOn
    (continuousOn_lyap.mono (cbox_subset_openStripFin hm))
  exact ⟨max K 0, le_max_right _ _, fun y hy =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hK y hy).trans (le_max_left _ _))⟩

end BlockBand.Diffusion
