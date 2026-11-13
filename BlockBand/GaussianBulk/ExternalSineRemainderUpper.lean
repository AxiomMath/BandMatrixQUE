module

public import BlockBand.GaussianBulk.ExternalSineRemainderCrossing

/-!
# The bound along the upper half of the grafted loop

The grafted level loop is the reflection of its upper half `nativeUpperPath`; the curve
integral along this upper half is bounded by combining a constant majorant on the outer pieces
with a graph majorant on the central piece.

Domain: `N > 0`, `0 < t ≤ tmax`, `0 < η ≤ levelHeight d t x₀`, arbitrary real `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology

/-- The upper half of the grafted level loop. -/
def nativeUpperPath {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (t tmax η x₀ : ℝ) (ht : 0 < t) :=
  graftedLevelUpperPath hN d t (x₀-graftedCentralRadius tmax η) (x₀+graftedCentralRadius tmax η) ht
    (raisedLevelMeshVertex d t (-graftedDeformationRadius d-Real.sqrt t)
      (graftedLevelMeshSpacing (-graftedDeformationRadius d-Real.sqrt t)
        (x₀-graftedCentralRadius tmax η) (Real.sqrt t/(2*(N : ℝ)^2))))
    (raisedLevelMeshVertex d t (x₀+graftedCentralRadius tmax η)
      (graftedLevelMeshSpacing (x₀+graftedCentralRadius tmax η)
        (graftedDeformationRadius d+Real.sqrt t) (Real.sqrt t/(2*(N : ℝ)^2))))
    (graftedLevelMeshCount (-graftedDeformationRadius d-Real.sqrt t)
      (x₀-graftedCentralRadius tmax η) (Real.sqrt t/(2*(N : ℝ)^2)))
    (graftedLevelMeshCount (x₀+graftedCentralRadius tmax η)
      (graftedDeformationRadius d+Real.sqrt t) (Real.sqrt t/(2*(N : ℝ)^2)))

/-- The grafted level loop is the reflection of its upper half (definitional). -/
theorem nativeGraftedLevelLoop_eq {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (t tmax η x₀ : ℝ)
    (ht : 0 < t) :
    nativeGraftedLevelLoop hN d t tmax η x₀ ht =
      reflectedLevelLoop (nativeUpperPath hN d t tmax η x₀ ht) := rfl

/-- Coordinates of a point of a segment. -/
theorem segment_point_coords (p q z : ℂ) (hz : z ∈ range (Path.segment p q)) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z.re = p.re + s*(q.re - p.re) ∧ z.im = p.im + s*(q.im - p.im) := by
  obtain ⟨⟨s, hs⟩, rfl⟩ := hz
  refine ⟨s, hs.1, hs.2, ?_, ?_⟩ <;>
  · rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    simp
    ring

/-- A raised mesh vertex lies `√(2√t h)` above the graph. -/
theorem raisedLevelMeshVertex_im_eq {N : ℕ} (d : Fin N → ℝ) (t A h : ℝ) (j : ℕ) :
    (raisedLevelMeshVertex d t A h j).im =
      levelHeight d t (raisedLevelMeshVertex d t A h j).re + Real.sqrt (2*Real.sqrt t*h) := by
  simp [raisedLevelMeshVertex]

/-- A vertical graft point between a raised vertex and the graph point at the same abscissa. -/
theorem graft_point_bounds {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (t c h : ℝ) (ht : 0 < t)
    (hh0 : 0 < h) (hh : h ≤ Real.sqrt t/(2*(N:ℝ)^2)) (p : ℂ) (hpre : p.re = c)
    (hpim : p.im = levelHeight d t c + Real.sqrt (2*Real.sqrt t*h)) (z : ℂ)
    (hz : z ∈ range (Path.segment p (actualLevelGraphPoint d t c)) ∨
      z ∈ range (Path.segment (actualLevelGraphPoint d t c) p)) :
    z.re = c ∧ levelHeight d t z.re ≤ |z.im| ∧
      |z.im| ≤ levelHeight d t z.re + 2*Real.sqrt t/N := by
  have hl := raisedLift_le hN t h ht hh
  have hl0 := Real.sqrt_nonneg (2*Real.sqrt t*h)
  have hy0 := (levelHeight_bounds hN d t c ht).1
  have hgre : (actualLevelGraphPoint d t c).re = c := by simp [actualLevelGraphPoint]
  have hgim : (actualLevelGraphPoint d t c).im = levelHeight d t c := by
    simp [actualLevelGraphPoint]
  have h2 : 2*Real.sqrt t/N = 2*(Real.sqrt t/N) := by ring
  have hfin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ w : ℂ, w.re = c →
      (w.im = levelHeight d t c + s * Real.sqrt (2*Real.sqrt t*h)) →
      w.re = c ∧ levelHeight d t w.re ≤ |w.im| ∧
        |w.im| ≤ levelHeight d t w.re + 2*Real.sqrt t/N := by
    intro s hs0 hs1 w hwre hwim
    have hpos : 0 ≤ w.im := by rw [hwim]; positivity
    rw [abs_of_nonneg hpos, hwre, hwim]
    refine ⟨rfl, by nlinarith, ?_⟩
    nlinarith
  rcases hz with hz | hz
  · obtain ⟨s, hs0, hs1, hre, him⟩ := segment_point_coords _ _ _ hz
    exact hfin (1 - s) (by linarith) (by linarith) z (by rw [hre, hpre, hgre]; ring)
      (by rw [him, hpim, hgim]; ring)
  · obtain ⟨s, hs0, hs1, hre, him⟩ := segment_point_coords _ _ _ hz
    exact hfin s hs0 hs1 z (by rw [hre, hpre, hgre]; ring) (by rw [him, hpim, hgim]; ring)

/-- **Bound along the upper half of the grafted level loop.** -/
theorem norm_curveIntegral_nativeUpperPath_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η rho x₀ xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hheight : η ≤ levelHeight d t x₀) (g : ℂ → ℂ) (K : Set ℂ) (hg : PieceIntegrable g K)
    (hK : range (nativeUpperPath hN d t tmax η x₀ ht) ⊆ K) (Kout : ℝ) (hKout : 0 ≤ Kout)
    (hout : ∀ z ∈ range (nativeUpperPath hN d t tmax η x₀ ht),
      OuterPoint d t x₀ (graftedCentralRadius tmax η) z → ‖g z‖ ≤ Kout)
    (hgr : ∀ x ∈ Icc (x₀ - graftedCentralRadius tmax η) (x₀ + graftedCentralRadius tmax η),
      x ≠ x₀ → ‖g (actualLevelGraphPoint d t x)‖ * ‖levelGraphVelocity d t x‖ ≤
        centralMajorant d E t tmax η rho x₀ (levelHeight d t x₀) xi zeta (x - x₀))
    (hrho : 0 < rho) (hpsi : levelPsi d t x₀ = E) :
    ‖curveIntegral (scalarForm g) (nativeUpperPath hN d t tmax η x₀ ht)‖ ≤
      Kout * ((2*graftedDeformationRadius d + 2*Real.sqrt t)*(1 + 2*N) + 4*Real.sqrt t/N) +
        centralCrossingBound N t tmax η rho xi := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hg0 := graftedCentralGeometry hN d t tmax η x₀ ht htmax hη hheight
  simp only at hg0
  obtain ⟨hLa, hax, hxb, hbR, hclose⟩ := hg0
  set r := graftedCentralRadius tmax η with hrdef
  have hr0 : 0 < r := by linarith
  set R₀ := graftedDeformationRadius d
  set Lx := -R₀ - Real.sqrt t
  set Rx := R₀ + Real.sqrt t
  set a := x₀ - r
  set b := x₀ + r
  set cap := Real.sqrt t/(2*(N:ℝ)^2) with hcap
  have hcap0 : 0 < cap := by positivity
  set hL := graftedLevelMeshSpacing Lx a cap
  set hR := graftedLevelMeshSpacing b Rx cap
  set ML := graftedLevelMeshCount Lx a cap
  set MR := graftedLevelMeshCount b Rx cap
  set vL := raisedLevelMeshVertex d t Lx hL
  set vR := raisedLevelMeshVertex d t b hR
  have hsL := graftedLevelMeshSpacing_bounds Lx a cap hLa hcap0
  have hsR := graftedLevelMeshSpacing_bounds b Rx cap hbR hcap0
  have hy0 : levelHeight d t x₀ = levelHeight d t x₀ := rfl
  have hpos : ∀ x ∈ Icc a b, 0 < levelHeight d t x := by
    intro x hx
    have := levelHeight_neighborhood_lower hN d t tmax η x₀ x ht htmax hη hheight (hclose x hx)
    linarith
  -- the five pieces
  set P1 := finiteLevelMeshPath vL ML
  set P2 := Path.segment (vL ML) (actualLevelGraphPoint d t a)
  set P3 := actualLevelGraphPath hN d t a b ht
  set P4 := Path.segment (actualLevelGraphPoint d t b) (vR 0)
  set P5 := finiteLevelMeshPath vR MR
  have hU : nativeUpperPath hN d t tmax η x₀ ht = P1.trans (P2.trans (P3.trans (P4.trans P5))) :=
    rfl
  have g1 := goodPath_finiteLevelMeshPath vL ML
  have g2 := goodPath_segment (vL ML) (actualLevelGraphPoint d t a)
  have g3 := goodPath_actualLevelGraphPath hN d t a b ht (by linarith) hpos
  have g4 := goodPath_segment (actualLevelGraphPoint d t b) (vR 0)
  have g5 := goodPath_finiteLevelMeshPath vR MR
  have hrU : range (nativeUpperPath hN d t tmax η x₀ ht) =
      range P1 ∪ (range P2 ∪ (range P3 ∪ (range P4 ∪ range P5))) := by
    rw [hU]; simp only [Path.trans_range]
  have m1 : range P1 ⊆ range (nativeUpperPath hN d t tmax η x₀ ht) := by
    rw [hrU]; exact subset_union_left
  have m2 : range P2 ⊆ range (nativeUpperPath hN d t tmax η x₀ ht) := by
    rw [hrU]; exact subset_union_left.trans subset_union_right
  have m3 : range P3 ⊆ range (nativeUpperPath hN d t tmax η x₀ ht) := by
    rw [hrU]; exact subset_union_left.trans (subset_union_right.trans subset_union_right)
  have m4 : range P4 ⊆ range (nativeUpperPath hN d t tmax η x₀ ht) := by
    rw [hrU]
    exact subset_union_left.trans (subset_union_right.trans
      (subset_union_right.trans subset_union_right))
  have m5 : range P5 ⊆ range (nativeUpperPath hN d t tmax η x₀ ht) := by
    rw [hrU]
    exact subset_union_right.trans (subset_union_right.trans
      (subset_union_right.trans subset_union_right))
  -- vertex coordinates
  have hvLre : (vL ML).re = a := (graftedLevelMesh_endpoint_re d t Lx a cap hLa hcap0).2
  have hvR0re : (vR 0).re = b := (graftedLevelMesh_endpoint_re d t b Rx cap hbR hcap0).1
  have hvLim : (vL ML).im = levelHeight d t a + Real.sqrt (2*Real.sqrt t*hL) := by
    rw [raisedLevelMeshVertex_im_eq, hvLre]
  have hvR0im : (vR 0).im = levelHeight d t b + Real.sqrt (2*Real.sqrt t*hR) := by
    rw [raisedLevelMeshVertex_im_eq, hvR0re]
  have hliftL := raisedLift_le hN t hL ht hsL.2
  have hliftR := raisedLift_le hN t hR ht hsR.2
  -- piece bounds
  have hMLh : Lx + ML*hL = a := by
    have := (graftedLevelMesh_endpoint_re d t Lx a cap hLa hcap0).2
    simpa [raisedLevelMeshVertex] using this
  have hMRh : b + MR*hR = Rx := by
    have := (graftedLevelMesh_endpoint_re d t b Rx cap hbR hcap0).2
    simpa [raisedLevelMeshVertex] using this
  have b1 : ‖curveIntegral (scalarForm g) P1‖ ≤ Kout * ((a - Lx)*(1 + 2*N) + Real.sqrt t/N) := by
    refine (norm_curveIntegral_finiteLevelMeshPath_le hg vL Kout ML (m1.trans hK)
      (fun z hz => hout z (m1 hz) ?_)).trans
      (mul_le_mul_of_nonneg_left (raisedMesh_length_le hN d t Lx a ht hLa) hKout)
    obtain ⟨h1, h2, h3, h4⟩ := finiteLevelMeshPath_raised_mem hN d t Lx hL ht hsL.1 hsL.2 ML z hz
    have him0 : 0 ≤ z.im := le_trans (levelHeight_bounds hN d t z.re ht).1 h3
    refine ⟨?_, by rw [abs_of_nonneg him0]; exact h3, by rw [abs_of_nonneg him0]; exact h4⟩
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have b5 : ‖curveIntegral (scalarForm g) P5‖ ≤ Kout * ((Rx - b)*(1 + 2*N) + Real.sqrt t/N) := by
    refine (norm_curveIntegral_finiteLevelMeshPath_le hg vR Kout MR (m5.trans hK)
      (fun z hz => hout z (m5 hz) ?_)).trans
      (mul_le_mul_of_nonneg_left (raisedMesh_length_le hN d t b Rx ht hbR) hKout)
    obtain ⟨h1, h2, h3, h4⟩ := finiteLevelMeshPath_raised_mem hN d t b hR ht hsR.1 hsR.2 MR z hz
    have him0 : 0 ≤ z.im := le_trans (levelHeight_bounds hN d t z.re ht).1 h3
    refine ⟨?_, by rw [abs_of_nonneg him0]; exact h3, by rw [abs_of_nonneg him0]; exact h4⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  have b2 : ‖curveIntegral (scalarForm g) P2‖ ≤ Kout * (Real.sqrt t/N) := by
    refine (norm_curveIntegral_segment_le g _ _ Kout (fun z hz => hout z (m2 hz) ?_)).trans ?_
    · obtain ⟨h1, h2, h3⟩ := graft_point_bounds hN d t a hL ht hsL.1 hsL.2 (vL ML) hvLre hvLim z
        (Or.inl hz)
      refine ⟨?_, h2, h3⟩
      rw [h1, show a - x₀ = -r by ring, abs_neg, abs_of_pos hr0]
    · apply mul_le_mul_of_nonneg_left _ hKout
      have : actualLevelGraphPoint d t a - vL ML = -((Real.sqrt (2*Real.sqrt t*hL) : ℝ) : ℂ) *
          Complex.I := by
        apply Complex.ext <;> simp [actualLevelGraphPoint, hvLre, hvLim]
      rw [this, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact hliftL
  have b4 : ‖curveIntegral (scalarForm g) P4‖ ≤ Kout * (Real.sqrt t/N) := by
    refine (norm_curveIntegral_segment_le g _ _ Kout (fun z hz => hout z (m4 hz) ?_)).trans ?_
    · obtain ⟨h1, h2, h3⟩ := graft_point_bounds hN d t b hR ht hsR.1 hsR.2 (vR 0) hvR0re hvR0im z
        (Or.inr hz)
      refine ⟨?_, h2, h3⟩
      rw [h1, show b - x₀ = r by ring, abs_of_pos hr0]
    · apply mul_le_mul_of_nonneg_left _ hKout
      have : vR 0 - actualLevelGraphPoint d t b = ((Real.sqrt (2*Real.sqrt t*hR) : ℝ) : ℂ) *
          Complex.I := by
        apply Complex.ext <;> simp [actualLevelGraphPoint, hvR0re, hvR0im]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact hliftR
  have b3 : ‖curveIntegral (scalarForm g) P3‖ ≤ centralCrossingBound N t tmax η rho xi := by
    have hpr : PositiveLevelRoot d t x₀ (levelHeight d t x₀) := by
      have hp := hpos x₀ ⟨by linarith, by linarith⟩
      exact levelHeight_root hN d t x₀ ht ((levelHeight_pos_iff hN d t x₀ ht).mp hp)
    obtain ⟨hI, hB⟩ := integral_centralGraphMajorant_le hN d E t tmax η rho x₀ (levelHeight d t x₀)
      xi zeta ht htmax hη hrho hpr hheight hpsi
    exact (norm_curveIntegral_actualLevelGraphPath_le hN d t a b ht (by linarith) hpos g _ x₀ hI
      hgr).trans hB
  -- assemble
  have r5 : range (P4.trans P5) ⊆ K := by
    rw [Path.trans_range]; exact union_subset (m4.trans hK) (m5.trans hK)
  have r4 : range (P3.trans (P4.trans P5)) ⊆ K := by
    rw [Path.trans_range]; exact union_subset (m3.trans hK) r5
  have r3 : range (P2.trans (P3.trans (P4.trans P5))) ⊆ K := by
    rw [Path.trans_range]; exact union_subset (m2.trans hK) r4
  have r2 : range (P1.trans (P2.trans (P3.trans (P4.trans P5)))) ⊆ K := by
    rw [Path.trans_range]; exact union_subset (m1.trans hK) r3
  have t5 := norm_curveIntegral_trans_le hg g4 g5 r5 b4 b5
  have t4 := norm_curveIntegral_trans_le hg g3 (g4.trans g5) r4 b3 t5
  have t3 := norm_curveIntegral_trans_le hg g2 (g3.trans (g4.trans g5)) r3 b2 t4
  have t2 := norm_curveIntegral_trans_le hg g1 (g2.trans (g3.trans (g4.trans g5))) r2 b1 t3
  rw [hU]
  refine t2.trans (le_of_eq_of_le rfl ?_)
  have hlen : (a - Lx) + (Rx - b) ≤ 2*R₀ + 2*Real.sqrt t := by
    simp only [a, b, Lx, Rx]; linarith
  have h2N : (0:ℝ) ≤ 1 + 2*N := by positivity
  have := mul_le_mul_of_nonneg_right hlen h2N
  have h4 : 4*Real.sqrt t/N = 4*(Real.sqrt t/N) := by ring
  rw [h4]
  nlinarith [mul_le_mul_of_nonneg_left this hKout]

end BlockBand.GaussianBulk
