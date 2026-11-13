module

public import BlockBand.GaussianBulk.LevelEnvelope
public import BlockBand.GaussianBulk.LevelNeighborhood

/-!
# The horizontal barrier for the level action

The level action is convex on `ℝ` and minimized at the point `x₀` where `ψ(x₀) = E`. Combined
with local curvature, this gives the uniform horizontal barrier
`(η²/(2 tmax²)) · min((x - x₀)², r|x - x₀|) ≤ Λ(x) - Λ(x₀)`, `r = η²/(4√tmax)`, whenever the
level height at `x₀` is at least `η` and `t ≤ tmax`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set Filter Topology

private theorem convex_min_of_zero_deriv {S : Set ℝ} {f : ℝ → ℝ}
    (hc : ConvexOn ℝ S f) {x₀ x : ℝ} (h₀ : x₀ ∈ S) (hx : x ∈ S)
    (hd : HasDerivAt f 0 x₀) : f x₀ ≤ f x := by
  rcases lt_trichotomy x₀ x with hlt | heq | hlt
  · have hs := hc.le_slope_of_hasDerivAt h₀ hx hlt hd
    rw [slope_def_field] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    linarith
  · rw [heq]
  · have hs := hc.slope_le_of_hasDerivAt hx h₀ hlt hd
    rw [slope_def_field] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr hlt)).mp hs
    linarith

/-- The level action is convex on `ℝ`. -/
theorem levelAction_convex {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t : ℝ) (ht : 0 < t) : ConvexOn ℝ univ (levelAction d E t) := by
  have hf : Differentiable ℝ (levelAction d E t) :=
    fun x => (hasDerivAt_levelAction_global hN d E t x ht).differentiableAt
  have hm : Monotone (deriv (levelAction d E t)) := by
    intro x y hxy
    rw [(hasDerivAt_levelAction_global hN d E t x ht).deriv,
      (hasDerivAt_levelAction_global hN d E t y ht).deriv]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right ((levelPsi_strictMono hN d t ht).monotone hxy) E) (le_of_lt ht)
  exact Monotone.convexOn_univ_of_deriv hf hm

/-- Every point with `ψ(x₀) = E` is a global minimum of the level action. -/
theorem levelAction_global_min {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x₀ x : ℝ) (ht : 0 < t) (hpsi : levelPsi d t x₀=E) :
    levelAction d E t x₀ ≤ levelAction d E t x := by
  apply convex_min_of_zero_deriv (levelAction_convex hN d E t ht) (mem_univ _) (mem_univ _)
  simpa only [hpsi,sub_self,zero_div] using hasDerivAt_levelAction_global hN d E t x₀ ht

private theorem local_quadratic_of_second_deriv
    (f : ℝ → ℝ) (x₀ r C : ℝ) (hr : 0 < r)
    (hf : Differentiable ℝ f) (h₀ : HasDerivAt f 0 x₀)
    (hdd : ∀ x, |x-x₀| ≤ r → DifferentiableAt ℝ (deriv f) x)
    (hcurv : ∀ x, |x-x₀| ≤ r → C ≤ deriv (deriv f) x)
    (x : ℝ) (hx : |x-x₀| ≤ r) :
    (C/2)*(x-x₀)^2 ≤ f x-f x₀ := by
  let g : ℝ → ℝ := fun u => f u-(C/2)*(u-x₀)^2
  let S : Set ℝ := Icc (x₀-r) (x₀+r)
  have hclose {u : ℝ} (hu : u ∈ S) : |u-x₀| ≤ r := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1,hu.2]
  have hpoly (u : ℝ) : HasDerivAt (fun z => (C/2)*(z-x₀)^2) (C*(u-x₀)) u := by
    have hh := (((hasDerivAt_id u).sub_const x₀).pow 2).const_mul (C/2)
    convert! hh using 1
    simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    ring
  have hG (u : ℝ) : HasDerivAt g (deriv f u-C*(u-x₀)) u := by
    exact (hf u).hasDerivAt.sub (hpoly u)
  have hGD : deriv g=(fun u => deriv f u-C*(u-x₀)) :=
    funext (fun u => (hG u).deriv)
  have hG₂ (u : ℝ) (hu : u ∈ S) :
      HasDerivAt (deriv g) (deriv (deriv f) u-C) u := by
    rw [hGD]
    have hh := (hdd u (hclose hu)).hasDerivAt.sub
      (((hasDerivAt_id u).sub_const x₀).const_mul C)
    convert! hh using 1
    simp only [mul_one]
  have hg : Continuous g := by
    exact (show Differentiable ℝ g from fun u => (hG u).differentiableAt).continuous
  have hconv : ConvexOn ℝ S g := by
    apply convexOn_of_deriv2_nonneg (convex_Icc _ _) hg.continuousOn
      (fun u _ => (hG u).differentiableAt.differentiableWithinAt)
      (fun u hu => (hG₂ u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    intro u hu
    change 0 ≤ deriv (deriv g) u
    rw [(hG₂ u (interior_subset hu)).deriv]
    exact sub_nonneg.mpr (hcurv u (hclose (interior_subset hu)))
  have hmem₀ : x₀ ∈ S := ⟨by linarith,by linarith⟩
  have hmem : x ∈ S := by
    rcases abs_le.mp hx with ⟨hl,hu⟩
    exact ⟨by linarith,by linarith⟩
  have hd₀ : HasDerivAt g 0 x₀ := by
    simpa only [h₀.deriv,sub_self,mul_zero] using hG x₀
  have hmin := convex_min_of_zero_deriv hconv hmem₀ hmem hd₀
  dsimp only [g] at hmin
  simp only [sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,sub_zero] at hmin
  linarith

/-- A convex function with quadratic growth `(C/2)(x - x₀)²` on `|x - x₀| ≤ r` satisfies
`(C/2) min((x - x₀)², r|x - x₀|) ≤ f(x) - f(x₀)` everywhere. -/
theorem convex_global_quadratic_linear_barrier (f : ℝ → ℝ) (x₀ r C : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (hc : ConvexOn ℝ univ f)
    (hq : ∀ x, |x-x₀| ≤ r → (C/2)*(x-x₀)^2 ≤ f x-f x₀) (x : ℝ) :
    (C/2)*min ((x-x₀)^2) (r*|x-x₀|) ≤ f x-f x₀ := by
  have hC₂ : 0 ≤ C/2 := by positivity
  by_cases hx : |x-x₀| ≤ r
  · exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC₂) (hq x hx)
  · have hfar : r < |x-x₀| := lt_of_not_ge hx
    have hdist : 0 < |x-x₀| := lt_trans hr hfar
    let lam := r/|x-x₀|
    let p := x₀+lam*(x-x₀)
    have hlam : 0 < lam := div_pos hr hdist
    have hlamone : lam ≤ 1 := (div_le_one₀ hdist).mpr (le_of_lt hfar)
    have hp : |p-x₀|=r := by
      have he : p-x₀=lam*(x-x₀) := by dsimp only [p];ring
      rw [he,abs_mul,abs_of_pos hlam]
      exact div_mul_cancel₀ _ (ne_of_gt hdist)
    have hconv := hc.2 (mem_univ x₀) (mem_univ x)
      (sub_nonneg.mpr hlamone) (le_of_lt hlam) (show (1-lam)+lam=1 by ring)
    have hpconv : f p ≤ f x₀+lam*(f x-f x₀) := by
      convert! hconv using 1
      · congr 1
        simp only [smul_eq_mul]
        dsimp only [p]
        ring
      · simp only [smul_eq_mul]
        ring
    have hqp := hq p (le_of_eq hp)
    have hsquare : (p-x₀)^2=r^2 := by rw [← sq_abs,hp]
    rw [hsquare] at hqp
    have hqlam : (C/2)*r^2 ≤ lam*(f x-f x₀) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hqlam (le_of_lt hdist)
    have he : lam*(f x-f x₀)*|x-x₀|=r*(f x-f x₀) := by
      dsimp only [lam]
      field_simp [ne_of_gt hdist]
    rw [he] at hmul
    have hlin : (C/2)*(r*|x-x₀|) ≤ f x-f x₀ := by
      apply (mul_le_mul_iff_right₀ hr).mp
      convert! hmul using 1
      ring
    exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC₂) hlin

/-- **Horizontal barrier.** If `ψ(x₀) = E` and the level height at `x₀` is at least `η`, then
`(η²/(2 tmax²)) min((x - x₀)², (η²/(4√tmax))|x - x₀|) ≤ Λ(x) - Λ(x₀)` for every real `x`. -/
theorem levelAction_horizontal_barrier {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax eta x₀ x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀) (hpsi : levelPsi d t x₀=E) :
    (eta^2/(2*tmax^2))*min ((x-x₀)^2)
      ((eta^2/(4*Real.sqrt tmax))*|x-x₀|) ≤
        levelAction d E t x-levelAction d E t x₀ := by
  let r := eta^2/(4*Real.sqrt tmax)
  let C := eta^2/tmax^2
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hr : 0 < r := div_pos (sq_pos_of_pos heta)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr htm))
  have hc : 0 ≤ C := div_nonneg (sq_nonneg eta) (sq_nonneg tmax)
  have hf : Differentiable ℝ (levelAction d E t) :=
    fun u => (hasDerivAt_levelAction_global hN d E t u ht).differentiableAt
  have hd₀ : HasDerivAt (levelAction d E t) 0 x₀ := by
    simpa only [hpsi,sub_self,zero_div] using hasDerivAt_levelAction_global hN d E t x₀ ht
  have hdd (u : ℝ) (hu : |u-x₀| ≤ r) : DifferentiableAt ℝ (deriv (levelAction d E t)) u := by
    have hy := levelHeight_neighborhood_lower hN d t tmax eta x₀ u ht htmax heta hheight hu
    have ha := (levelHeight_pos_iff hN d t u ht).mp (lt_of_lt_of_le (by linarith : 0 < eta/2) hy)
    exact (hasDerivAt_deriv_levelAction hN d E t u ht ha).differentiableAt
  have hcurv (u : ℝ) (hu : |u-x₀| ≤ r) : C ≤ deriv (deriv (levelAction d E t)) u :=
    deriv2_levelAction_neighborhood_lower hN d E t tmax eta x₀ u ht htmax heta hheight hu
  have hh := convex_global_quadratic_linear_barrier (levelAction d E t) x₀ r C hr hc
    (levelAction_convex hN d E t ht)
    (fun u hu => local_quadratic_of_second_deriv _ x₀ r C hr hf hd₀ hdd hcurv u hu) x
  have he : C/2=eta^2/(2*tmax^2) := by dsimp only [C];field_simp
  simpa only [he,r] using hh

/-- The horizontal barrier at the saddle of a solution of the finite MDE with `Im m ≥ v`, with
`η = tmin · v`. -/
theorem levelAction_MDE_horizontal_barrier {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmin tmax v x : ℝ) (m : ℂ) (htmin : 0 < tmin)
    (ht : tmin ≤ t) (htmax : t ≤ tmax) (hv : 0 < v) (hm : v ≤ m.im)
    (hMDE : FiniteMDE d E t m) :
    ((tmin*v)^2/(2*tmax^2))*min ((x-(saddlePoint E t m).re)^2)
      (((tmin*v)^2/(4*Real.sqrt tmax))*|x-(saddlePoint E t m).re|) ≤
        levelAction d E t x-levelAction d E t (saddlePoint E t m).re := by
  have htp := lt_of_lt_of_le htmin ht
  have hmp := lt_of_lt_of_le hv hm
  apply levelAction_horizontal_barrier hN d E t tmax (tmin*v) _ x htp htmax
    (mul_pos htmin hv) _ (levelPsi_at_saddle hN d E t m htp hmp hMDE)
  rw [levelHeight_at_saddle hN d E t m htp hmp hMDE]
  exact saddlePoint_im_lower E t tmin v m htmin ht (le_of_lt hv) hm

end BlockBand.GaussianBulk
