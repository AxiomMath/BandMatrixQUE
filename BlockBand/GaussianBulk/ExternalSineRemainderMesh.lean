module

public import BlockBand.GaussianBulk.ExternalSineRemainderOuter

/-!
# Geometry of the outer parts of the grafted loop

Elementary bounds on the raised meshes forming the outer parts of the grafted level loop.

* `raisedLift_le`: the mesh lift `√(2√t h) ≤ √t/N` for `h ≤ √t/(2N²)`;
* `finiteLevelMeshPath_raised_mem`: real-part range and height window on a raised mesh;
* `levelHeight_outer_endpoint`: `y = 0` at `±(Σ|d_j| + √t)`;
* `raisedMesh_length_le`: total mesh length `≤ (B - A)(1 + 2N) + √t/N`.

Domain: `N > 0`, `t > 0`, arbitrary real `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set

/-- A point of the outer parts: off the central strip, raised above the graph by at most
`2√t/N` (in modulus of the imaginary part). -/
def OuterPoint {N : ℕ} (d : Fin N → ℝ) (t x₀ r : ℝ) (z : ℂ) : Prop :=
  r ≤ |z.re - x₀| ∧ levelHeight d t z.re ≤ |z.im| ∧
    |z.im| ≤ levelHeight d t z.re + 2*Real.sqrt t/N

/-- Outer points are closed under conjugation. -/
theorem OuterPoint.star {N : ℕ} {d : Fin N → ℝ} {t x₀ r : ℝ} {z : ℂ}
    (h : OuterPoint d t x₀ r z) : OuterPoint d t x₀ r (star z) := by
  simpa [OuterPoint] using h

/-- The mesh lift is at most `√t/N`. -/
theorem raisedLift_le {N : ℕ} (hN : 0 < N) (t h : ℝ) (ht : 0 < t)
    (hh : h ≤ Real.sqrt t/(2*(N:ℝ)^2)) :
    Real.sqrt (2*Real.sqrt t*h) ≤ Real.sqrt t/N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hs := Real.sqrt_nonneg t
  rw [show Real.sqrt t/N = Real.sqrt ((Real.sqrt t/N)^2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : 2*Real.sqrt t*h ≤ 2*Real.sqrt t*(Real.sqrt t/(2*(N:ℝ)^2)) :=
    mul_le_mul_of_nonneg_left hh (by positivity)
  refine h1.trans (le_of_eq ?_)
  field_simp

/-- Points of a raised mesh with spacing `0 < h ≤ √t/(2N²)` from `A`: real part in
`[A, A + M h]`, height in `[y(x), y(x) + 2√t/N]`. -/
theorem finiteLevelMeshPath_raised_mem {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (t A h : ℝ)
    (ht : 0 < t) (hh0 : 0 < h) (hh : h ≤ Real.sqrt t/(2*(N:ℝ)^2)) (M : ℕ) (z : ℂ)
    (hz : z ∈ range (finiteLevelMeshPath (raisedLevelMeshVertex d t A h) M)) :
    A ≤ z.re ∧ z.re ≤ A + M*h ∧ levelHeight d t z.re ≤ z.im ∧
      z.im ≤ levelHeight d t z.re + 2*Real.sqrt t/N := by
  have hlift := raisedLift_le hN t h ht hh
  induction M with
  | zero =>
    have hz' : z = raisedLevelMeshVertex d t A h 0 := by simpa [finiteLevelMeshPath] using hz
    subst hz'
    have hs : 0 ≤ Real.sqrt (2*Real.sqrt t*h) := Real.sqrt_nonneg _
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    simp only [raisedLevelMeshVertex, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add, Nat.cast_zero, zero_mul]
    refine ⟨le_rfl, le_rfl, by linarith, ?_⟩
    have : 0 ≤ Real.sqrt t/N := by positivity
    have h2 : 2*Real.sqrt t/N = 2*(Real.sqrt t/N) := by ring
    linarith
  | succ M ih =>
    have hrange : range (finiteLevelMeshPath (raisedLevelMeshVertex d t A h) (M + 1)) =
        range (finiteLevelMeshPath (raisedLevelMeshVertex d t A h) M) ∪
          range (Path.segment (raisedLevelMeshVertex d t A h M)
            (raisedLevelMeshVertex d t A h (M + 1))) := Path.trans_range _ _
    rw [hrange] at hz
    rcases hz with hz | hz
    · obtain ⟨h1, h2, h3, h4⟩ := ih hz
      refine ⟨h1, ?_, h3, h4⟩
      push_cast
      linarith
    · obtain ⟨⟨s, hs⟩, rfl⟩ := hz
      have hs0 := hs.1
      have hs1 := hs.2
      have hpt : (Path.segment (raisedLevelMeshVertex d t A h M)
          (raisedLevelMeshVertex d t A h (M + 1))) ⟨s, hs⟩ =
            (((1-s)*(A + (M:ℝ)*h) + s*(A + ((M:ℝ)+1)*h) : ℝ) : ℂ) +
              ((raisedLevelChord d t (A + (M:ℝ)*h) (A + ((M:ℝ)+1)*h) h s : ℝ) : ℂ) *
                Complex.I := by
        rw [Path.segment_apply, AffineMap.lineMap_apply_module]
        apply Complex.ext
        · simp [raisedLevelMeshVertex]
          ring
        · simp [raisedLevelMeshVertex, raisedLevelChord]
          ring
      have hre : ((((1-s)*(A + (M:ℝ)*h) + s*(A + ((M:ℝ)+1)*h) : ℝ) : ℂ) +
          ((raisedLevelChord d t (A + (M:ℝ)*h) (A + ((M:ℝ)+1)*h) h s : ℝ) : ℂ) *
            Complex.I).re = (1-s)*(A + (M:ℝ)*h) + s*(A + ((M:ℝ)+1)*h) := by simp
      have him : ((((1-s)*(A + (M:ℝ)*h) + s*(A + ((M:ℝ)+1)*h) : ℝ) : ℂ) +
          ((raisedLevelChord d t (A + (M:ℝ)*h) (A + ((M:ℝ)+1)*h) h s : ℝ) : ℂ) *
            Complex.I).im = raisedLevelChord d t (A + (M:ℝ)*h) (A + ((M:ℝ)+1)*h) h s := by simp
      have hab : A + (M:ℝ)*h ≤ A + ((M:ℝ)+1)*h := by nlinarith
      have hba : A + ((M:ℝ)+1)*h - (A + (M:ℝ)*h) ≤ h := by nlinarith
      have hc := raisedLevelChord_bounds hN d t _ _ h s ht hab hba hs0 hs1
      simp only at hc
      have h2 : 2*Real.sqrt t/N = 2*(Real.sqrt t/N) := by ring
      rw [hpt, hre, him]
      refine ⟨by nlinarith, ?_, by linarith [hc.1], by linarith [hc.2.1]⟩
      push_cast
      nlinarith

/-- The level graph vanishes at the outer endpoints `±(Σ|d_j| + √t)`. -/
theorem levelHeight_outer_endpoint {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (t : ℝ) (ht : 0 < t) :
    levelHeight d t (-graftedDeformationRadius d - Real.sqrt t) = 0 ∧
      levelHeight d t (graftedDeformationRadius d + Real.sqrt t) = 0 := by
  have hb := graftedDeformationRadius_bounds d
  have h0 (x : ℝ) : levelHeight d t x = 0 ∨ 0 < levelHeight d t x :=
    (levelHeight_bounds hN d t x ht).1.eq_or_lt.imp (fun h => h.symm) id
  constructor
  · rcases h0 (-graftedDeformationRadius d - Real.sqrt t) with h | h
    · exact h
    · have := levelHeight_support_interval hN d t _ _ _ ht hb h
      linarith [this.1]
  · rcases h0 (graftedDeformationRadius d + Real.sqrt t) with h | h
    · exact h
    · have := levelHeight_support_interval hN d t _ _ _ ht hb h
      linarith [this.2]

/-- Total length of the ceil mesh from `A` to `B` with cap `√t/(2N²)`. -/
theorem raisedMesh_length_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (t A B : ℝ) (ht : 0 < t)
    (hAB : A < B) :
    (∑ j : Fin (graftedLevelMeshCount A B (Real.sqrt t/(2*(N:ℝ)^2))),
        ‖raisedLevelMeshVertex d t A (graftedLevelMeshSpacing A B (Real.sqrt t/(2*(N:ℝ)^2)))
            (j.val+1) -
          raisedLevelMeshVertex d t A (graftedLevelMeshSpacing A B (Real.sqrt t/(2*(N:ℝ)^2)))
            j.val‖) ≤
      (B - A) * (1 + 2*N) + Real.sqrt t/N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  set cap := Real.sqrt t/(2*(N:ℝ)^2) with hcap
  have hcap0 : 0 < cap := by positivity
  set h := graftedLevelMeshSpacing A B cap
  set M := graftedLevelMeshCount A B cap
  have hsb := graftedLevelMeshSpacing_bounds A B cap hAB hcap0
  have hM : (0:ℝ) < M := by exact_mod_cast graftedLevelMeshCount_pos A B cap hAB hcap0
  have hMh : (M:ℝ) * h = B - A := by
    have hM' : (graftedLevelMeshCount A B cap : ℝ) ≠ 0 := ne_of_gt hM
    simp only [h, graftedLevelMeshSpacing, M]
    field_simp
  have hMle : (M:ℝ) ≤ (B - A)/cap + 1 := (Nat.ceil_lt_add_one (by
    exact div_nonneg (sub_nonneg.mpr hAB.le) hcap0.le)).le
  have hlen := raisedLevelMesh_total_length hN d t A h ht hsb.1.le M
  have hlift := raisedLift_le hN t h ht hsb.2
  refine hlen.trans ?_
  have h1 : (M:ℝ) * (h + Real.sqrt (2*Real.sqrt t*h)) ≤ (B - A) + M * (Real.sqrt t/N) := by
    rw [mul_add, hMh]
    have := mul_le_mul_of_nonneg_left hlift hM.le
    linarith
  have h2 : (M:ℝ) * (Real.sqrt t/N) ≤ ((B - A)/cap + 1) * (Real.sqrt t/N) :=
    mul_le_mul_of_nonneg_right hMle (by positivity)
  have h3 : ((B - A)/cap + 1) * (Real.sqrt t/N) = (B - A) * (2*N) + Real.sqrt t/N := by
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    rw [hcap]
    field_simp
  nlinarith

end BlockBand.GaussianBulk
