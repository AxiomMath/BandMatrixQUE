module

public import BlockBand.GaussianBulk.ExternalSineRemainderUpper

/-!
# The remainder bound on the whole grafted loop

The curve integral over the grafted level loop of any function dominated by
`remainderMajorant` is at most `loopRemainderBound`. The lower half is handled by `∫_{γ̄} f = conj ∫_γ f*` and the conjugation symmetry of the
majorant (`remainderMajorant_star`).

Domain: `N > 0`, `0 < t ≤ tmax`, `ρ > 0`, `0 < η ≤ y₀ = levelHeight d t x₀`,
`levelPsi d t x₀ = E`, `|ξ|/(tρ) ≤ N c r`, arbitrary real `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology

/-- The polynomial length factor of the outer parts of one half of the loop. -/
def upperOuterLength {N : ℕ} (d : Fin N → ℝ) (t : ℝ) : ℝ :=
  (2*graftedDeformationRadius d + 2*Real.sqrt t)*(1 + 2*N) + 4*Real.sqrt t/N

/-- The total loop bound. -/
def loopRemainderBound {N : ℕ} (d : Fin N → ℝ) (t tmax η rho xi : ℝ) : ℝ :=
  2*(outerDecayConstant N t tmax η rho xi * upperOuterLength d t +
      centralCrossingBound N t tmax η rho xi) +
    outerDecayConstant N t tmax η rho xi * (4*Real.sqrt t/N)

/-- The outer decay constant is nonnegative. -/
theorem outerDecayConstant_nonneg (N : ℕ) (t tmax η rho xi : ℝ) (htm : 0 < tmax) (hη : 0 < η) :
    0 ≤ outerDecayConstant N t tmax η rho xi := by
  unfold outerDecayConstant verticalMassConstant graftedCentralRadius
  have := Real.sqrt_pos.mpr htm
  positivity

/-- A closing vertical segment at an outer endpoint consists of outer points. -/
theorem closing_segment_outer {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (t x₀ r c h : ℝ)
    (ht : 0 < t) (hh : h ≤ Real.sqrt t/(2*(N:ℝ)^2)) (hc : r ≤ |c - x₀|)
    (hy : levelHeight d t c = 0) (p : ℂ) (hpre : p.re = c)
    (hpim : p.im = levelHeight d t c + Real.sqrt (2*Real.sqrt t*h)) (z : ℂ)
    (hz : z ∈ range (Path.segment p (star p)) ∨ z ∈ range (Path.segment (star p) p)) :
    OuterPoint d t x₀ r z ∧ ‖star p - p‖ ≤ 2*(Real.sqrt t/N) := by
  have hl := raisedLift_le hN t h ht hh
  have hl0 := Real.sqrt_nonneg (2*Real.sqrt t*h)
  rw [hy, zero_add] at hpim
  have hlen : ‖star p - p‖ ≤ 2*(Real.sqrt t/N) := by
    have : star p - p = ((-2*p.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, hpim,
      abs_mul, abs_of_nonneg hl0, show |(-2:ℝ)| = 2 by norm_num]
    linarith
  refine ⟨?_, hlen⟩
  have h2 : 2*Real.sqrt t/N = 2*(Real.sqrt t/N) := by ring
  have key : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → z.re = c →
      z.im = Real.sqrt (2*Real.sqrt t*h) * (1 - 2*s) → OuterPoint d t x₀ r z := by
    intro s hs0 hs1 hre him
    refine ⟨by rw [hre]; exact hc, by rw [hre, hy]; exact abs_nonneg _, ?_⟩
    rw [hre, hy, zero_add, him, abs_mul, abs_of_nonneg hl0]
    have : |1 - 2*s| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h3 := mul_le_mul_of_nonneg_left this hl0
    have : 0 ≤ Real.sqrt t/N := by positivity
    linarith
  rcases hz with hz | hz
  · obtain ⟨s, hs0, hs1, hre, him⟩ := segment_point_coords _ _ _ hz
    refine key s hs0 hs1 (by rw [hre]; simp [hpre]) ?_
    rw [him]; simp [hpim]; ring
  · obtain ⟨s, hs0, hs1, hre, him⟩ := segment_point_coords _ _ _ hz
    refine key (1 - s) (by linarith) (by linarith) (by rw [hre]; simp [hpre]) ?_
    rw [him]; simp [hpim]; ring

/-- Range facts for a reflected loop. -/
theorem reflectedLevelLoop_range_facts {a b : ℂ} (U : Path a b) :
    range U ⊆ range (reflectedLevelLoop U) ∧
      (∀ z ∈ range U, star z ∈ range (reflectedLevelLoop U)) ∧
      range (Path.segment a (star a)) ⊆ range (reflectedLevelLoop U) ∧
      range (Path.segment (star b) b) ⊆ range (reflectedLevelLoop U) := by
  have hrange : range (reflectedLevelLoop U) = range U ∪ (range (Path.segment a (star a)) ∪
      (range (U.map Complex.continuous_conj) ∪ range (Path.segment (star b) b))) := by
    unfold reflectedLevelLoop; simp only [Path.trans_range, Path.symm_range]
  rw [hrange]
  refine ⟨subset_union_left, fun z hz => ?_, subset_union_left.trans subset_union_right,
    subset_union_right.trans (subset_union_right.trans subset_union_right)⟩
  exact Or.inr (Or.inr (Or.inl ((range_map_conj U (star z)).mpr (by simpa using hz))))

/-- Norm bound along a reflected loop from bounds on the upper half (for `f` and `f*`) and on
the two closing segments. -/
theorem norm_curveIntegral_reflectedLevelLoop_le {f : ℂ → ℂ} {K : Set ℂ}
    (hf : PieceIntegrable f K) {a b : ℂ} (U : Path a b) (gU : GoodPath U)
    (hK : range (reflectedLevelLoop U) ⊆ K) {X Y : ℝ}
    (bU : ‖curveIntegral (scalarForm f) U‖ ≤ X)
    (bU' : ‖curveIntegral (scalarForm (fun z => star (f (star z)))) U‖ ≤ X)
    (bA : ‖curveIntegral (scalarForm f) (Path.segment a (star a))‖ ≤ Y)
    (bB : ‖curveIntegral (scalarForm f) (Path.segment (star b) b)‖ ≤ Y) :
    ‖curveIntegral (scalarForm f) (reflectedLevelLoop U)‖ ≤ 2*X + 2*Y := by
  have hloop : reflectedLevelLoop U = U.symm.trans ((Path.segment a (star a)).trans
      ((U.map Complex.continuous_conj).trans (Path.segment (star b) b))) := rfl
  have hrange : range (reflectedLevelLoop U) = range U ∪ (range (Path.segment a (star a)) ∪
      (range (U.map Complex.continuous_conj) ∪ range (Path.segment (star b) b))) := by
    rw [hloop]; simp only [Path.trans_range, Path.symm_range]
  rw [hrange] at hK
  have gA := goodPath_segment a (star a)
  have gB := goodPath_segment (star b) b
  have gC := gU.map_conj
  have bC : ‖curveIntegral (scalarForm f) (U.map Complex.continuous_conj)‖ ≤ X := by
    rw [curveIntegral_map_conj_eq, norm_star]; exact bU'
  have bS : ‖curveIntegral (scalarForm f) U.symm‖ ≤ X := by
    rw [curveIntegral_symm, norm_neg]; exact bU
  have rCB : range ((U.map Complex.continuous_conj).trans (Path.segment (star b) b)) ⊆ K := by
    rw [Path.trans_range]
    exact union_subset (fun z hz => hK (Or.inr (Or.inr (Or.inl hz))))
      (fun z hz => hK (Or.inr (Or.inr (Or.inr hz))))
  have rACB : range ((Path.segment a (star a)).trans
      ((U.map Complex.continuous_conj).trans (Path.segment (star b) b))) ⊆ K := by
    rw [Path.trans_range]
    exact union_subset (fun z hz => hK (Or.inr (Or.inl hz))) rCB
  have rAll : range (U.symm.trans ((Path.segment a (star a)).trans
      ((U.map Complex.continuous_conj).trans (Path.segment (star b) b)))) ⊆ K := by
    rw [Path.trans_range, Path.symm_range]
    exact union_subset (fun z hz => hK (Or.inl hz)) rACB
  have t3 := norm_curveIntegral_trans_le hf gC gB rCB bC bB
  have t2 := norm_curveIntegral_trans_le hf gA (gC.trans gB) rACB bA t3
  have t1 := norm_curveIntegral_trans_le hf gU.symm (gA.trans (gC.trans gB)) rAll bS t2
  rw [hloop]
  refine t1.trans (le_of_eq ?_)
  ring

/-- **The whole loop.** If `‖f‖ ≤ remainderMajorant` on the loop off `Re z = x₀`, then the curve
integral of `f` over the grafted level loop is at most `loopRemainderBound`. -/
theorem norm_curveIntegral_nativeGraftedLevelLoop_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η rho x₀ xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hheight : η ≤ levelHeight d t x₀) (hrho : 0 < rho) (hpsi : levelPsi d t x₀ = E)
    (hscale : |xi|/(t*rho) ≤ (N:ℝ)*(η^2/(2*tmax^2))*graftedCentralRadius tmax η)
    (f : ℂ → ℂ) (K : Set ℂ) (hf : PieceIntegrable f K) (hKstar : ∀ z ∈ K, star z ∈ K)
    (hK : range (nativeGraftedLevelLoop hN d t tmax η x₀ ht) ⊆ K)
    (hfm : ∀ z ∈ range (nativeGraftedLevelLoop hN d t tmax η x₀ ht), z.re ≠ x₀ →
      ‖f z‖ ≤ remainderMajorant d E t rho x₀ xi zeta z) :
    ‖curveIntegral (scalarForm f) (nativeGraftedLevelLoop hN d t tmax η x₀ ht)‖ ≤
      loopRemainderBound d t tmax η rho xi := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hg0 := graftedCentralGeometry hN d t tmax η x₀ ht htmax hη hheight
  simp only at hg0
  obtain ⟨hLa, hax, hxb, hbR, hclose⟩ := hg0
  have hr0 : 0 < graftedCentralRadius tmax η := by linarith
  have hpr : PositiveLevelRoot d t x₀ (levelHeight d t x₀) :=
    levelHeight_root hN d t x₀ ht ((levelHeight_pos_iff hN d t x₀ ht).mp (by linarith))
  have hKout : 0 ≤ outerDecayConstant N t tmax η rho xi :=
    outerDecayConstant_nonneg N t tmax η rho xi htm hη
  have hpos : ∀ x ∈ Icc (x₀ - graftedCentralRadius tmax η) (x₀ + graftedCentralRadius tmax η),
      0 < levelHeight d t x := by
    intro x hx
    have := levelHeight_neighborhood_lower hN d t tmax η x₀ x ht htmax hη hheight (hclose x hx)
    linarith
  have gU : GoodPath (nativeUpperPath hN d t tmax η x₀ ht) :=
    goodPath_graftedLevelUpperPath hN d t _ _ ht (by linarith) _ _ _ _ hpos
  rw [nativeGraftedLevelLoop_eq] at hK hfm ⊢
  obtain ⟨mU, hstarU, mA, mB⟩ := reflectedLevelLoop_range_facts (nativeUpperPath hN d t tmax η x₀ ht)
  -- outer bound for `f`
  have hout : ∀ z ∈ range (reflectedLevelLoop (nativeUpperPath hN d t tmax η x₀ ht)),
      OuterPoint d t x₀ (graftedCentralRadius tmax η) z →
        ‖f z‖ ≤ outerDecayConstant N t tmax η rho xi := by
    intro z hz hO
    have hre : z.re ≠ x₀ := by
      intro h; have := hO.1; rw [h, sub_self, abs_zero] at this; linarith
    refine (hfm z hz hre).trans ?_
    exact remainderMajorant_le_outer hN d E t tmax η rho x₀ (levelHeight d t x₀) xi zeta ht htmax
      hη hrho hpr hheight hpsi hscale z hO.1
      (levelAction_sub_verticalRealAction_le hN d E t z.re z.im ht hO.2.1 hO.2.2)
  -- central bound for the majorant
  have hcent : ∀ x ∈ Icc (x₀ - graftedCentralRadius tmax η) (x₀ + graftedCentralRadius tmax η),
      x ≠ x₀ → remainderMajorant d E t rho x₀ xi zeta (actualLevelGraphPoint d t x) *
        ‖levelGraphVelocity d t x‖ ≤
          centralMajorant d E t tmax η rho x₀ (levelHeight d t x₀) xi zeta (x - x₀) := by
    intro x hx hx0
    have ha : |x - x₀| ≤ graftedCentralRadius tmax η :=
      abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h := remainderMajorant_central_le hN d E t tmax η rho x₀ (levelHeight d t x₀) xi zeta
      ht htmax hη hrho hpr hheight (x - x₀) (sub_ne_zero.mpr hx0) ha
    rw [show x₀ + (x - x₀) = x by ring] at h
    exact h
  have hgraph_mem : ∀ x ∈ Icc (x₀ - graftedCentralRadius tmax η) (x₀ + graftedCentralRadius tmax η),
      actualLevelGraphPoint d t x ∈ range (nativeUpperPath hN d t tmax η x₀ ht) :=
    fun x hx => graftedLevelUpperPath_contains hN d t _ _ x ht (by linarith) hx _ _ _ _
  have hgre : ∀ x, (actualLevelGraphPoint d t x).re = x := fun x => by simp [actualLevelGraphPoint]
  -- the upper half for `f` and `f*`
  have bU := norm_curveIntegral_nativeUpperPath_le hN d E t tmax η rho x₀ xi zeta ht htmax hη
    hheight f K hf (mU.trans hK) _ hKout (fun z hz hO => hout z (mU hz) hO)
    (fun x hx hx0 => by
      have h1 := hfm _ (mU (hgraph_mem x hx)) (by rw [hgre]; exact hx0)
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans (hcent x hx hx0))
    hrho hpsi
  have bU' := norm_curveIntegral_nativeUpperPath_le hN d E t tmax η rho x₀ xi zeta ht htmax hη
    hheight (fun z => star (f (star z))) K (hf.conj hKstar) (mU.trans hK) _ hKout
    (fun z hz hO => by
      simp only [norm_star]
      exact hout _ (hstarU z hz) hO.star)
    (fun x hx hx0 => by
      simp only [norm_star]
      have h1 := hfm _ (hstarU _ (hgraph_mem x hx)) (by simp [hgre]; exact hx0)
      rw [remainderMajorant_star hN d E t rho x₀ xi zeta ht hrho] at h1
      exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans (hcent x hx hx0))
    hrho hpsi
  -- closing segments
  have hy := levelHeight_outer_endpoint hN d t ht
  have hcap0 : 0 < Real.sqrt t/(2*(N:ℝ)^2) := by positivity
  have hsL := graftedLevelMeshSpacing_bounds _ _ _ hLa hcap0
  have hsR := graftedLevelMeshSpacing_bounds _ _ _ hbR hcap0
  have hAre := (graftedLevelMesh_endpoint_re d t _ _ _ hLa hcap0).1
  have hBre := (graftedLevelMesh_endpoint_re d t _ _ _ hbR hcap0).2
  have cA := closing_segment_outer hN d t x₀ (graftedCentralRadius tmax η) _ _ ht hsL.2
    (by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith) hy.1 _ hAre
    (by rw [raisedLevelMeshVertex_im_eq, hAre])
  have cB := closing_segment_outer hN d t x₀ (graftedCentralRadius tmax η) _ _ ht hsR.2
    (by rw [abs_of_pos (by linarith)]; linarith) hy.2 _ hBre
    (by rw [raisedLevelMeshVertex_im_eq, hBre])
  have bA := (norm_curveIntegral_segment_le f _ _ _ (fun z hz =>
      hout z (mA hz) (cA z (Or.inl hz)).1)).trans
      (mul_le_mul_of_nonneg_left (cA _ (Or.inl ⟨0, Path.source _⟩)).2 hKout)
  have bB := (norm_curveIntegral_segment_le f _ _ _ (fun z hz =>
      hout z (mB hz) (cB z (Or.inr hz)).1)).trans
      (mul_le_mul_of_nonneg_left ((norm_sub_rev _ _).le.trans
        (cB _ (Or.inl ⟨0, Path.source _⟩)).2) hKout)
  refine (norm_curveIntegral_reflectedLevelLoop_le hf _ gU hK bU bU' bA bB).trans (le_of_eq ?_)
  unfold loopRemainderBound upperOuterLength
  ring

end BlockBand.GaussianBulk
