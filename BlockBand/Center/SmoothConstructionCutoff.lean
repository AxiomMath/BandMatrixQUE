module

public import BlockBand.Center.SmoothConstructionRoot

/-!
# The smooth center `j^{sm}_e = χ_E(E) χ(ε_e²) j_e`

Constants for a `ϑ`-bulk rank `α` (`κ = κ_α = rankMargin`, `k = ctrLevel κ`, `θ_k < κ`):
`ε₁ = cst0.ε₁ b κ` (half the certificate threshold `ε_cert(s, θ_k)`), the energy cutoff `χ_E = 1` on `|E| ≤ 2 - κ`, `0` for `|E| ≥ 2 - (κ + θ_k)/2`, and the
residual cutoff `χ(ε²) = 1` for `ε² ≤ ε₁²`, `0` for `ε² ≥ (3ε₁/2)²` (`ContDiffBump`s; the squared
residual `scnEps2` is smooth, unlike `ε_e`).

* `scnPhi b ϑ`: the smooth center (zero for `p.b ≠ b`, non-bulk ranks, non-Hermitian inputs, or
  when no Dyson root exists); `scn_abs_phi_le` (`|Φ| ≤ 1`), `scn_measurable_phi` (Borel, Lusin–
  Souslin as in `CenterMeasurable`), `scn_phi_zero_of_energy`, `scn_phi_agree` (`Φ = j_e` on the regular
  domain of `cst0`), `scn_support_root` (a root exists on the cutoff support, also at exterior
  poles, by `scn_root_of_frequently`), **`scn_phi_contDiff`** (`C^∞` along every shift line).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open Matrix Filter Topology MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Layers BlockBand.Palm
open scoped ComplexConjugate Matrix.Norms.L2Operator ContDiff

/-!
## 1. Bumps
-/

section Bump

/-- A smooth bump on `ℝ`: `1` on `[-a, a]`, `0` off `(-r, r)` (for `0 < a < r`; `0` otherwise). -/
def scnBump (a r : ℝ) (x : ℝ) : ℝ :=
  if h : 0 < a ∧ a < r then (⟨a, r, h.1, h.2⟩ : ContDiffBump (0 : ℝ)) x else 0

theorem scn_bump_contDiff (a r : ℝ) : ContDiff ℝ ∞ (scnBump a r) := by
  unfold scnBump
  by_cases h : 0 < a ∧ a < r
  · simp only [dite_eq_left h]; exact ContDiffBump.contDiff _
  · simp only [dite_eq_right h]; exact contDiff_const

theorem scn_bump_nonneg (a r x : ℝ) : 0 ≤ scnBump a r x := by
  unfold scnBump; split_ifs
  · exact ContDiffBump.nonneg _
  · exact le_rfl

theorem scn_bump_le_one (a r x : ℝ) : scnBump a r x ≤ 1 := by
  unfold scnBump; split_ifs
  · exact ContDiffBump.le_one _
  · norm_num

theorem scn_abs_bump_le (a r x : ℝ) : |scnBump a r x| ≤ 1 := by
  rw [abs_of_nonneg (scn_bump_nonneg a r x)]; exact scn_bump_le_one a r x

theorem scn_bump_one {a r x : ℝ} (ha : 0 < a) (har : a < r) (hx : |x| ≤ a) : scnBump a r x = 1 := by
  unfold scnBump
  rw [dite_eq_left ⟨ha, har⟩]
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx

theorem scn_bump_zero {a r x : ℝ} (hx : r ≤ |x|) : scnBump a r x = 0 := by
  unfold scnBump
  split_ifs with h
  · refine ContDiffBump.zero_of_le_dist _ ?_
    rw [Real.dist_eq, sub_zero]; exact hx
  · rfl

theorem scn_bump_eventually_zero {a r x₀ : ℝ} (hx : r < |x₀|) :
    ∀ᶠ x in 𝓝 x₀, scnBump a r x = 0 := by
  have : ∀ᶠ x in 𝓝 x₀, r < |x| := continuous_abs.continuousAt.eventually (lt_mem_nhds hx)
  filter_upwards [this] with x hx'
  exact scn_bump_zero hx'.le

/-- The derivative of a bump is bounded. -/
theorem scn_bump_deriv_bound (a r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv (scnBump a r) x| ≤ C := by
  have hc : Continuous (deriv (scnBump a r)) :=
    (scn_bump_contDiff a r).continuous_deriv (by simp)
  have hsupp : HasCompactSupport (deriv (scnBump a r)) := by
    refine HasCompactSupport.deriv ?_
    unfold scnBump
    by_cases h : 0 < a ∧ a < r
    · simp only [dite_eq_left h]; exact ContDiffBump.hasCompactSupport _
    · simp only [dite_eq_right h]; exact HasCompactSupport.zero
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hsupp
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have := hC x
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

end Bump

/-!
## 2. Bulk constants
-/

section Constants

variable {p : Parameters}

/-- The cutoff margin `θ' = (κ + θ_{k(κ)})/2`. -/
def scnMid (κ : ℝ) : ℝ := (κ + ctrTheta (ctrLevel κ)) / 2

theorem scn_theta_lt {κ : ℝ} (hκ : 0 < κ) : ctrTheta (ctrLevel κ) < κ := by
  unfold ctrTheta ctrLevel
  have h1 : 2 / κ ≤ (⌈2 / κ⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_lt_iff₀ (by positivity)]
  rw [div_le_iff₀ hκ] at h1
  nlinarith

theorem scn_rankMargin_pos {ϑ : ℝ} (hϑ : 0 < ϑ) {α : Fin p.N} (hα : IsBulkRank p ϑ α) :
    0 < rankMargin p α :=
  (by linarith : (0 : ℝ) < ϑ / 2).trans_le (ctr_rankMargin_ge hϑ α hα)

theorem scn_rankMargin_le_one (α : Fin p.N) : rankMargin p α ≤ 1 := by
  unfold rankMargin
  have := abs_nonneg (classicalLocation p α)
  linarith

/-- The ordering `0 < 2 - κ < 2 - θ' < 2 - θ_k` of the energy cutoff. -/
theorem scn_mid_bounds {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    0 < 2 - κ ∧ 2 - κ < 2 - scnMid κ ∧ 2 - scnMid κ < 2 - ctrTheta (ctrLevel κ) := by
  have h := scn_theta_lt hκ
  unfold scnMid
  refine ⟨by linarith, by linarith, by linarith⟩

theorem ctrTheta_anti {j k : ℕ} (h : j ≤ k) : ctrTheta k ≤ ctrTheta j := by
  unfold ctrTheta
  have : (j : ℝ) ≤ k := by exact_mod_cast h
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-- `ε₁` of `cst0` is half the certificate threshold. -/
theorem scn_cst0_eps1 (b κ : ℝ) :
    cst0.ε₁ b κ = (ctrCert (ctrC b) (ctrTheta (ctrLevel κ))).1 / 2 := rfl

end Constants

/-!
## 3. The smooth center
-/

section Phi

variable {p : Parameters} {e : ZMod p.n}

/-- **The smooth center** `j^{sm}_e(E) = χ_E(E) χ(ε_e²) j_e(E)`, with the
unclipped center formula at the (unique) Dyson root; `0` for `p.b ≠ b`, non-`ϑ`-bulk ranks,
non-Hermitian inputs, or when no root exists. -/
def scnPhi (b ϑ : ℝ) (p : Parameters) (α : Fin p.N) (e : ZMod p.n) (H : p.SiteMatrix) (E : ℝ) :
    ℝ := by
  classical
  exact if p.b = b ∧ IsBulkRank p ϑ α ∧ H.IsHermitian ∧ ∃ ζ, IsDysonRoot p e H E ζ then
    scnBump (2 - rankMargin p α) (2 - scnMid (rankMargin p α)) E *
      scnBump 1 (9 / 4) (scnEps2 p e H E / cst0.ε₁ p.b (rankMargin p α) ^ 2) *
      scnU p e (compressedResolvent p e H E (scnRoot p e H E))
  else 0

theorem scn_phi_of_good {b ϑ : ℝ} {α : Fin p.N} {H : p.SiteMatrix} {E : ℝ}
    (h : p.b = b ∧ IsBulkRank p ϑ α ∧ H.IsHermitian ∧ ∃ ζ, IsDysonRoot p e H E ζ) :
    scnPhi b ϑ p α e H E =
      scnBump (2 - rankMargin p α) (2 - scnMid (rankMargin p α)) E *
        scnBump 1 (9 / 4) (scnEps2 p e H E / cst0.ε₁ p.b (rankMargin p α) ^ 2) *
        scnU p e (compressedResolvent p e H E (scnRoot p e H E)) := by
  unfold scnPhi; rw [ite_eq_left h]

theorem scn_phi_of_not {b ϑ : ℝ} {α : Fin p.N} {H : p.SiteMatrix} {E : ℝ}
    (h : ¬ (p.b = b ∧ IsBulkRank p ϑ α ∧ H.IsHermitian ∧ ∃ ζ, IsDysonRoot p e H E ζ)) :
    scnPhi b ϑ p α e H E = 0 := by
  unfold scnPhi; rw [ite_eq_right h]

/-- `|j^{sm}_e| ≤ 1`. -/
theorem scn_abs_phi_le (b ϑ : ℝ) (α : Fin p.N) (H : p.SiteMatrix) (E : ℝ) :
    |scnPhi b ϑ p α e H E| ≤ 1 := by
  by_cases h : p.b = b ∧ IsBulkRank p ϑ α ∧ H.IsHermitian ∧ ∃ ζ, IsDysonRoot p e H E ζ
  · rw [scn_phi_of_good h, abs_mul, abs_mul]
    have h1 := scn_abs_bump_le (2 - rankMargin p α) (2 - scnMid (rankMargin p α)) E
    have h2 := scn_abs_bump_le 1 (9 / 4) (scnEps2 p e H E / cst0.ε₁ p.b (rankMargin p α) ^ 2)
    have h3 := scn_abs_scnU_root_le h.2.2.1 (scn_root_spec h.2.2.2)
    have := mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3 (abs_nonneg _)
      (by norm_num)
    simpa using this
  · rw [scn_phi_of_not h, abs_zero]; norm_num

/-- Support: `Φ(·, E) = 0` for `|E| ≥ 2 - θ'`. -/
theorem scn_phi_zero_of_energy {b ϑ : ℝ} {α : Fin p.N} {H : p.SiteMatrix} {E : ℝ}
    (hE : 2 - scnMid (rankMargin p α) ≤ |E|) : scnPhi b ϑ p α e H E = 0 := by
  by_cases h : p.b = b ∧ IsBulkRank p ϑ α ∧ H.IsHermitian ∧ ∃ ζ, IsDysonRoot p e H E ζ
  · rw [scn_phi_of_good h, scn_bump_zero hE, zero_mul, zero_mul]
  · exact scn_phi_of_not h

/-- `Φ = 0` where `ε_e² ≥ (3ε₁/2)²`. -/
theorem scn_phi_zero_of_eps {b ϑ : ℝ} {α : Fin p.N} {H : p.SiteMatrix} {E : ℝ}
    (hε : 9 / 4 ≤ |scnEps2 p e H E / cst0.ε₁ p.b (rankMargin p α) ^ 2|) :
    scnPhi b ϑ p α e H E = 0 := by
  by_cases h : p.b = b ∧ IsBulkRank p ϑ α ∧ H.IsHermitian ∧ ∃ ζ, IsDysonRoot p e H E ζ
  · rw [scn_phi_of_good h, scn_bump_zero hε, mul_zero, zero_mul]
  · exact scn_phi_of_not h

/-- **Agreement on the regular domain** of `cst0`: `j^{sm}_e = j_e`. -/
theorem scn_phi_agree {b ϑ : ℝ} (hϑ : 0 < ϑ) {α : Fin p.N} (hpb : p.b = b)
    (hα : IsBulkRank p ϑ α) {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ}
    (hdom : InCenterDomain p e cst0 α H E) : scnPhi b ϑ p α e H E = dysonCenter p e cst0 α H E := by
  obtain ⟨hI, hε, ζ, hroot, hdisk⟩ := hdom
  have hκ := scn_rankMargin_pos hϑ hα
  have hκ1 := scn_rankMargin_le_one α
  obtain ⟨h0, h1, -⟩ := scn_mid_bounds hκ hκ1
  rw [scn_phi_of_good ⟨hpb, hα, hH, ζ, hroot⟩]
  have hE : |E| ≤ 2 - rankMargin p α := by
    unfold bulkInterval at hI
    exact abs_le.mpr ⟨by linarith [hI.1], hI.2⟩
  rw [scn_bump_one h0 h1 hE, one_mul]
  have hε1 := cst0.ε₁_pos p.b (rankMargin p α)
  have heps : scnEps2 p e H E / cst0.ε₁ p.b (rankMargin p α) ^ 2 ≤ 1 := by
    have hcR : centerResidual p e H E ^ 2 = scnEps2 p e H E := by
      rw [scn_centerResidual_eq, Real.sq_sqrt (by unfold scnEps2; positivity)]
    rw [div_le_one (by positivity), ← hcR]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hε 2
  have hpos : 0 ≤ scnEps2 p e H E / cst0.ε₁ p.b (rankMargin p α) ^ 2 := by
    unfold scnEps2; positivity
  rw [scn_bump_one (by norm_num) (by norm_num) (by rw [abs_of_nonneg hpos]; exact heps), one_mul]
  have hdomI : InCenterDomain p e cst0 α H E := ⟨hI, hε, ζ, hroot, hdisk⟩
  have hsel := (ctr_dysonRoot_spec ⟨ζ, hroot, hdisk⟩).1
  have hr : scnRoot p e H E = dysonRoot p e (cst0.ρ₀ p.b (rankMargin p α)) H E :=
    scn_root_eq hH hsel
  rw [hr, ctr_dysonCenter_of_mem hdomI, ctr_centerFormula_eq hH hsel]
  rfl

end Phi

/-!
## 4. Measurability
-/

section Measurable

variable {p : Parameters} {e : ZMod p.n}

open Classical in
/-- Functions of the Hermitian input and its Dyson root are Borel (Lusin–Souslin; the root is
unique). -/
theorem scn_measurable_rootFun (G : (p.SiteMatrix × ℝ) × ℂ → ℝ) (hG : Measurable G) :
    Measurable (fun x : p.SiteMatrix × ℝ =>
      if x.1.IsHermitian ∧ ∃ ζ, IsDysonRoot p e x.1 x.2 ζ then
        G (x, scnRoot p e x.1 x.2) else 0) := by
  let _ : PolishSpace p.SiteMatrix := inferInstanceAs (PolishSpace (p.Site → p.Site → ℂ))
  set S : Set ((p.SiteMatrix × ℝ) × ℂ) :=
    {y | y.1.1.IsHermitian ∧ IsDysonRoot p e y.1.1 y.1.2 y.2} with hSdef
  have hS : MeasurableSet S :=
    (ctr_measurableSet_hermitian.preimage (measurable_fst.comp measurable_fst)).inter
      ctr_measurableSet_root
  have hinj : Set.InjOn Prod.fst S := by
    intro y₁ h₁ y₂ h₂ h
    refine Prod.ext h ?_
    have h₂' : IsDysonRoot p e y₁.1.1 y₁.1.2 y₂.2 := by rw [h]; exact h₂.2
    exact ctr_root_unique h₁.1 h₁.2 h₂'
  set D : Set (p.SiteMatrix × ℝ) := {x | x.1.IsHermitian ∧ ∃ ζ, IsDysonRoot p e x.1 x.2 ζ}
  have hDeq : D = Prod.fst '' S := by
    ext x
    constructor
    · rintro ⟨hH, ζ, hr⟩; exact ⟨(x, ζ), ⟨hH, hr⟩, rfl⟩
    · rintro ⟨y, ⟨hH, hr⟩, rfl⟩; exact ⟨hH, y.2, hr⟩
  have hD : MeasurableSet D := by
    rw [hDeq]; exact hS.image_of_measurable_injOn measurable_fst hinj
  have hroot_of : ∀ y ∈ S, scnRoot p e y.1.1 y.1.2 = y.2 := fun y hy => scn_root_eq hy.1 hy.2
  intro B hB
  set f := fun x : p.SiteMatrix × ℝ =>
    if x.1.IsHermitian ∧ ∃ ζ, IsDysonRoot p e x.1 x.2 ζ then G (x, scnRoot p e x.1 x.2) else 0
  have hT : MeasurableSet (Prod.fst '' (S ∩ G ⁻¹' B)) :=
    (hS.inter (hG hB)).image_of_measurable_injOn measurable_fst (hinj.mono Set.inter_subset_left)
  have heq : f ⁻¹' B = Prod.fst '' (S ∩ G ⁻¹' B) ∪ (Dᶜ ∩ {_x | (0 : ℝ) ∈ B}) := by
    ext x
    constructor
    · intro hx
      by_cases hxD : x ∈ D
      · left
        rw [hDeq] at hxD
        obtain ⟨y, hy, rfl⟩ := hxD
        refine ⟨y, ⟨hy, ?_⟩, rfl⟩
        have hfx : f y.1 = G (y.1, scnRoot p e y.1.1 y.1.2) := by
          simp only [f]; rw [ite_eq_left ⟨hy.1, y.2, hy.2⟩]
        change G y ∈ B
        have : G y = f y.1 := by rw [hfx, hroot_of y hy]
        rw [this]; exact hx
      · right
        refine ⟨hxD, ?_⟩
        have hfx : f x = 0 := by
          simp only [f]
          exact ite_eq_right (show ¬ (x.1.IsHermitian ∧ ∃ ζ, IsDysonRoot p e x.1 x.2 ζ) from hxD)
        change (0 : ℝ) ∈ B
        rw [← hfx]; exact hx
    · rintro (⟨y, ⟨hy, hyB⟩, rfl⟩ | ⟨hxD, h0⟩)
      · change f y.1 ∈ B
        simp only [f]; rw [ite_eq_left ⟨hy.1, y.2, hy.2⟩, hroot_of y hy]
        exact hyB
      · change f x ∈ B
        simp only [f]
        rw [ite_eq_right (show ¬ (x.1.IsHermitian ∧ ∃ ζ, IsDysonRoot p e x.1 x.2 ζ) from hxD)]
        exact h0
  rw [heq]
  exact hT.union (hD.compl.inter (MeasurableSet.const _))

theorem scn_measurable_eps2 :
    Measurable (fun x : p.SiteMatrix × ℝ => scnEps2 p e x.1 x.2) := by
  have h := (ctr_measurable_centerResidual (p := p) (i := e)).pow_const 2
  have heq : (fun x : p.SiteMatrix × ℝ => scnEps2 p e x.1 x.2) =
      fun x => centerResidual p e x.1 x.2 ^ 2 := by
    funext x
    rw [scn_centerResidual_eq, Real.sq_sqrt (by unfold scnEps2; positivity)]
  rw [heq]; exact h

theorem scn_continuous_scnU : Continuous (scnU p e) := by
  unfold scnU
  refine Complex.continuous_re.comp (continuous_const.mul ?_)
  exact (continuous_const.mul continuous_id.matrix_conjTranspose |>.mul continuous_id).matrix_trace

open Classical in
/-- **Borel measurability of the smooth center** in `(H, E)`. -/
theorem scn_measurable_phi (b ϑ : ℝ) (α : Fin p.N) :
    Measurable (fun x : p.SiteMatrix × ℝ => scnPhi b ϑ p α e x.1 x.2) := by
  by_cases hc : p.b = b ∧ IsBulkRank p ϑ α
  · set G : (p.SiteMatrix × ℝ) × ℂ → ℝ := fun y =>
      scnBump (2 - rankMargin p α) (2 - scnMid (rankMargin p α)) y.1.2 *
        scnBump 1 (9 / 4) (scnEps2 p e y.1.1 y.1.2 / cst0.ε₁ p.b (rankMargin p α) ^ 2) *
        scnU p e (compressedResolvent p e y.1.1 y.1.2 y.2)
    have hG : Measurable G := by
      refine (((scn_bump_contDiff _ _).continuous.measurable.comp
        (measurable_snd.comp measurable_fst)).mul ((scn_bump_contDiff _ _).continuous.measurable.comp
        ((scn_measurable_eps2.comp measurable_fst).div_const _))).mul ?_
      exact scn_continuous_scnU.measurable.comp ctr_measurable_compressed
    have heq : (fun x : p.SiteMatrix × ℝ => scnPhi b ϑ p α e x.1 x.2) =
        fun x => if x.1.IsHermitian ∧ ∃ ζ, IsDysonRoot p e x.1 x.2 ζ then
          G (x, scnRoot p e x.1 x.2) else 0 := by
      funext x
      by_cases h : x.1.IsHermitian ∧ ∃ ζ, IsDysonRoot p e x.1 x.2 ζ
      · rw [ite_eq_left h, scn_phi_of_good ⟨hc.1, hc.2, h⟩]
      · rw [ite_eq_right h, scn_phi_of_not (fun h' => h ⟨h'.2.2.1, h'.2.2.2⟩)]
    rw [heq]
    exact scn_measurable_rootFun (e := e) G hG
  · have heq : (fun x : p.SiteMatrix × ℝ => scnPhi b ϑ p α e x.1 x.2) = fun _ => 0 :=
      funext fun x => scn_phi_of_not fun h => hc ⟨h.1, h.2.1⟩
    rw [heq]; exact measurable_const

end Measurable

/-!
## 5. Roots on the cutoff support and smoothness along the shift lines
-/

section Smooth

variable {p : Parameters} {e : ZMod p.n}

/-- **A root exists on the cutoff support**, also at exterior poles: for `|E| < 2 - θ_k` and
`ε_e < ε_cert(s, θ_k)` there is a Dyson root with `Im ζ ≥ s v₀(k)` (certificate off the poles,
`scn_root_of_frequently` at the finitely many poles of the line). -/
theorem scn_support_root {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {k : ℕ} (x₀ : (ZMod p.n → ℝ) × ℝ)
    (hE : |x₀.2| < 2 - ctrTheta k)
    (hε : centerResidual p e (scnLine H₀ x₀) x₀.2 < (ctrCert (splitS p) (ctrTheta k)).1) :
    ∃ ζ, IsDysonRoot p e (scnLine H₀ x₀) x₀.2 ζ ∧
      splitS p * (ctrCert (splitS p) (ctrTheta k)).2.2.2 ≤ ζ.im := by
  have hHl := scn_line_isHermitian hH x₀
  by_cases hdet : (exteriorBlock p e (scnLine H₀ x₀) - (x₀.2 : ℂ) • 1).det ≠ 0
  · exact scn_cert_root hHl hdet hE.le hε.le
  · set c := splitS p
    have hc : 0 < c := ctr_splitS_pos
    have hc1 : c < 1 := by
      have : c ≤ p.b := min_le_right _ _
      linarith [p.b_lt_half]
    have hspec := ctrCert_spec hc hc1 (ctrTheta_pos k) (ctrTheta_le_two k)
    have hv : 0 < (ctrCert c (ctrTheta k)).2.2.2 := hspec.2.1.2.2.2.2.2
    have hy : 0 < c * (ctrCert c (ctrTheta k)).2.2.2 := mul_pos hc hv
    have hd := scn_eventually_det_ne (exteriorBlock p e (scnLine H₀ x₀)) x₀.2
    have h2 : |x₀.2| < 2 := hE.trans_le (by linarith [ctrTheta_pos k])
    have hcont : ContinuousAt (fun E : ℝ => centerResidual p e (scnLine H₀ (x₀.1, E)) E) x₀.2 := by
      have hc2 := (scn_contDiffAt_eps2 (e := e) hH hb hbd (x := (x₀.1, x₀.2)) h2).continuousAt
      have hl : ContinuousAt (fun E : ℝ => ((x₀.1, E) : (ZMod p.n → ℝ) × ℝ)) x₀.2 :=
        (continuous_const.prodMk continuous_id).continuousAt
      exact Real.continuous_sqrt.continuousAt.comp (hc2.comp hl)
    have hε' : ∀ᶠ E in 𝓝 x₀.2,
        centerResidual p e (scnLine H₀ (x₀.1, E)) E < (ctrCert c (ctrTheta k)).1 :=
      hcont.eventually (gt_mem_nhds hε)
    have hE' : ∀ᶠ E in 𝓝 x₀.2, |E| < 2 - ctrTheta k :=
      continuous_abs.continuousAt.eventually (gt_mem_nhds hE)
    have hev : ∀ᶠ E in 𝓝[≠] x₀.2, ∃ ζ, IsDysonRoot p e (scnLine H₀ (x₀.1, E)) E ζ ∧
        c * (ctrCert c (ctrTheta k)).2.2.2 ≤ ζ.im := by
      filter_upwards [hd, nhdsWithin_le_nhds hε', nhdsWithin_le_nhds hE'] with E hdE hεE hEE
      exact scn_cert_root (scn_line_isHermitian hH _) hdE hEE.le hεE.le
    exact scn_root_of_frequently hH hb hbd x₀.1 hy hev.frequently

/-- The smooth expression of the center at the root, `(s/2) Im(W⁻¹Tr P_eℛ - W⁻¹Tr P_{e+1}ℛ)/Im ζ`. -/
def scnUexpr (p : Parameters) (e : ZMod p.n) (H₀ : p.SiteMatrix) (x : (ZMod p.n → ℝ) × ℝ) : ℝ :=
  splitS p / 2 *
    (tgtTraceCLM e e (scnPsi p e H₀ (x, scnRoot p e (scnLine H₀ x) x.2))⁻¹ -
      tgtTraceCLM e (e + 1) (scnPsi p e H₀ (x, scnRoot p e (scnLine H₀ x) x.2))⁻¹).im /
    (scnRoot p e (scnLine H₀ x) x.2).im

theorem scn_scnU_root_eq {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {x : (ZMod p.n → ℝ) × ℝ}
    (hx : IsDysonRoot p e (scnLine H₀ x) x.2 (scnRoot p e (scnLine H₀ x) x.2)) :
    scnU p e (compressedResolvent p e (scnLine H₀ x) x.2 (scnRoot p e (scnLine H₀ x) x.2)) =
      scnUexpr p e H₀ x := by
  rw [scn_scnU_eq (scn_line_isHermitian hH x) x.2 hx.1.ne'
    (scn_psi_det_ne hH hb hbd (x, _) hx.1.ne')]
  rfl

theorem scn_contDiffAt_Uexpr {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {x₀ : (ZMod p.n → ℝ) × ℝ} {ζ₀ : ℂ}
    (hroot : IsDysonRoot p e (scnLine H₀ x₀) x₀.2 ζ₀) :
    ContDiffAt ℝ ∞ (scnUexpr p e H₀) x₀ := by
  obtain ⟨hζ, -⟩ := scn_root_contDiffAt hH hb hbd hroot
  have hr := scn_root_spec ⟨ζ₀, hroot⟩
  have hpair : ContDiffAt ℝ ∞ (fun x => (x, scnRoot p e (scnLine H₀ x) x.2)) x₀ :=
    contDiffAt_id.prodMk hζ
  have hdet0 := scn_psi_det_ne hH hb hbd (x₀, scnRoot p e (scnLine H₀ x₀) x₀.2) hr.1.ne'
  have hinv := (scn_contDiffAt_psi_inv (e := e) H₀ hdet0).comp x₀ hpair
  have hτ : ∀ k' : ZMod p.n, ContDiffAt ℝ ∞ (fun x => tgtTraceCLM e k'
      (scnPsi p e H₀ (x, scnRoot p e (scnLine H₀ x) x.2))⁻¹) x₀ := fun k' =>
    (tgtTraceCLM e k').contDiff.contDiffAt.comp x₀ hinv
  unfold scnUexpr
  refine (contDiffAt_const.mul (Complex.imCLM.contDiff.contDiffAt.comp x₀
    ((hτ e).sub (hτ (e + 1))))).div (Complex.imCLM.contDiff.contDiffAt.comp x₀ hζ) ?_
  exact hr.1.ne'

/-- **`j^{sm}_e` is `C^∞` along every shift line** through Hermitian, ring-banded `H₀` with
invertible exterior bonds, jointly in `(ξ, E)`. -/
theorem scn_phi_contDiff (b ϑ : ℝ) (hϑ : 0 < ϑ) (α : Fin p.N) {H₀ : p.SiteMatrix}
    (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀) (hbd : ExteriorBondsInvertible p e H₀) :
    ContDiff ℝ ∞ (fun x : (ZMod p.n → ℝ) × ℝ => scnPhi b ϑ p α e (scnLine H₀ x) x.2) := by
  by_cases hc : p.b = b ∧ IsBulkRank p ϑ α
  swap
  · have : (fun x : (ZMod p.n → ℝ) × ℝ => scnPhi b ϑ p α e (scnLine H₀ x) x.2) = fun _ => 0 :=
      funext fun x => scn_phi_of_not fun h => hc ⟨h.1, h.2.1⟩
    rw [this]; exact contDiff_const
  obtain ⟨hpb, hα⟩ := hc
  set κ := rankMargin p α with hκdef
  have hκ := scn_rankMargin_pos hϑ hα
  have hκ1 := scn_rankMargin_le_one α
  obtain ⟨h0, h1, h2⟩ := scn_mid_bounds hκ hκ1
  set k := ctrLevel κ
  set a := cst0.ε₁ p.b κ
  have ha : 0 < a := cst0.ε₁_pos _ _
  rw [contDiff_iff_contDiffAt]
  intro x₀
  by_cases hEo : 2 - scnMid κ < |x₀.2|
  · have hE : ∀ᶠ x in 𝓝 x₀, 2 - scnMid κ < |x.2| :=
      (continuous_abs.comp continuous_snd).continuousAt.eventually (lt_mem_nhds hEo)
    have : ∀ᶠ x in 𝓝 x₀, scnPhi b ϑ p α e (scnLine H₀ x) x.2 = 0 := by
      filter_upwards [hE] with x hx
      exact scn_phi_zero_of_energy hx.le
    exact contDiffAt_const.congr_of_eventuallyEq this
  push Not at hEo
  have hθ := ctrTheta_pos k
  have hE2 : |x₀.2| < 2 := by linarith
  have hcE := scn_contDiffAt_eps2 (e := e) hH hb hbd hE2
  by_cases hεo : 9 / 4 * a ^ 2 < scnEps2 p e (scnLine H₀ x₀) x₀.2
  · have hev : ∀ᶠ x in 𝓝 x₀, 9 / 4 * a ^ 2 < scnEps2 p e (scnLine H₀ x) x.2 :=
      hcE.continuousAt.eventually (lt_mem_nhds hεo)
    have : ∀ᶠ x in 𝓝 x₀, scnPhi b ϑ p α e (scnLine H₀ x) x.2 = 0 := by
      filter_upwards [hev] with x hx
      refine scn_phi_zero_of_eps ?_
      have hpos : 0 < scnEps2 p e (scnLine H₀ x) x.2 / a ^ 2 :=
        div_pos (lt_of_le_of_lt (by positivity) hx) (by positivity)
      rw [abs_of_pos hpos, le_div_iff₀ (by positivity)]
      exact hx.le
    exact contDiffAt_const.congr_of_eventuallyEq this
  push Not at hεo
  have hcert : (ctrCert (splitS p) (ctrTheta k)).1 = 2 * a := by
    simp only [a]; rw [scn_cst0_eps1, ← ctr_splitS_eq]; ring
  have hcR : centerResidual p e (scnLine H₀ x₀) x₀.2 < (ctrCert (splitS p) (ctrTheta k)).1 := by
    rw [hcert, scn_centerResidual_eq]
    have : Real.sqrt (scnEps2 p e (scnLine H₀ x₀) x₀.2) ≤ 3 / 2 * a := by
      rw [show 3 / 2 * a = Real.sqrt ((3 / 2 * a) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  obtain ⟨ζ₀, hroot, -⟩ := scn_support_root hH hb hbd x₀ (by linarith) hcR
  obtain ⟨-, hev⟩ := scn_root_contDiffAt hH hb hbd hroot
  have hloc : ∀ᶠ x in 𝓝 x₀, scnPhi b ϑ p α e (scnLine H₀ x) x.2 =
      scnBump (2 - κ) (2 - scnMid κ) x.2 *
        scnBump 1 (9 / 4) (scnEps2 p e (scnLine H₀ x) x.2 / a ^ 2) * scnUexpr p e H₀ x := by
    filter_upwards [hev] with x hx
    rw [scn_phi_of_good ⟨hpb, hα, scn_line_isHermitian hH x, _, hx⟩,
      scn_scnU_root_eq hH hb hbd hx]
  have hcut : ContDiffAt ℝ ∞ (fun x : (ZMod p.n → ℝ) × ℝ => scnBump (2 - κ) (2 - scnMid κ) x.2 *
      scnBump 1 (9 / 4) (scnEps2 p e (scnLine H₀ x) x.2 / a ^ 2)) x₀ :=
    ((scn_bump_contDiff _ _).contDiffAt.comp x₀ contDiffAt_snd).mul
      ((scn_bump_contDiff _ _).contDiffAt.comp x₀ (hcE.div_const _))
  exact (hcut.mul (scn_contDiffAt_Uexpr hH hb hbd hroot)).congr_of_eventuallyEq hloc

end Smooth

end BlockBand.Center
