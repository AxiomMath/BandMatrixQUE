module
public import BlockBand.GaussianBulk.GraftedResolventCentral
public import BlockBand.GaussianBulk.GraftedLevelEnclosure

/-!
# Winding of the grafted level loop

The resolvent integral of the grafted level loop around every source point `d_j` is `2πi`:
the upper path has an explicit logarithmic primitive, and the reflection and the two vertical
connectors contribute the branch jumps.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set MeasureTheory

private theorem graftedResolvent_trans_log {a b c : ℂ} (p : ℝ)
    (γ : Path a b) (δ : Path b c)
    (hγ : CurveIntegrable (graftedResolventForm p) γ ∧
      curveIntegral (graftedResolventForm p) γ = Complex.log (b-(p : ℂ))-Complex.log (a-(p : ℂ)))
    (hδ : CurveIntegrable (graftedResolventForm p) δ ∧
      curveIntegral (graftedResolventForm p) δ = Complex.log (c-(p : ℂ))-Complex.log (b-(p : ℂ))) :
    CurveIntegrable (graftedResolventForm p) (γ.trans δ) ∧
      curveIntegral (graftedResolventForm p) (γ.trans δ) =
        Complex.log (c-(p : ℂ))-Complex.log (a-(p : ℂ)) := by
  constructor
  · exact hγ.1.trans hδ.1
  · rw [curveIntegral_trans hγ.1 hδ.1,hγ.2,hδ.2]
    ring

/-- The upper path of the grafted loop (both meshes and the central graph) is resolvent-integrable,
with integral the difference of principal logarithms at its endpoints. -/
theorem graftedLevelUpperPath_resolvent_log {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t a b p : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (vL vR : ℕ → ℂ) (ML MR : ℕ)
    (hL : ∀ j ≤ ML, 0 < (vL j).im) (hR : ∀ j ≤ MR, 0 < (vR j).im)
    (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x) :
    CurveIntegrable (graftedResolventForm p) (graftedLevelUpperPath hN d t a b ht vL vR ML MR) ∧
      curveIntegral (graftedResolventForm p) (graftedLevelUpperPath hN d t a b ht vL vR ML MR) =
        Complex.log (vR MR-(p : ℂ))-Complex.log (vL 0-(p : ℂ)) := by
  have ha : 0 < (actualLevelGraphPoint d t a).im := by
    simpa [actualLevelGraphPoint] using hheight a ⟨le_rfl,hab⟩
  have hb : 0 < (actualLevelGraphPoint d t b).im := by
    simpa [actualLevelGraphPoint] using hheight b ⟨hab,le_rfl⟩
  exact graftedResolvent_trans_log p _ _
    (graftedResolvent_finite_upper_mesh_log p vL ML hL)
    (graftedResolvent_trans_log p _ _
      (graftedResolvent_upper_segment_log p _ _ (hL ML le_rfl) ha)
      (graftedResolvent_trans_log p _ _
        (actualLevelGraphPath_resolvent_log hN d t a b p ht hab hheight)
        (graftedResolvent_trans_log p _ _
          (graftedResolvent_upper_segment_log p _ _ hb (hR 0 (by omega)))
          (graftedResolvent_finite_upper_mesh_log p vR MR hR))))

/-- A reflected loop enclosing `p` whose upper path has a principal-log primitive has resolvent
integral `2πi`. -/
theorem reflectedLevelLoop_resolvent {a b : ℂ} (p : ℝ) (upper : Path a b)
    (ha : 0 < a.im) (hb : 0 < b.im) (hpa : a.re < p) (hpb : p < b.re)
    (hupper : CurveIntegrable (graftedResolventForm p) upper ∧
      curveIntegral (graftedResolventForm p) upper = Complex.log (b-(p : ℂ))-Complex.log (a-(p : ℂ))) :
    CurveIntegrable (graftedResolventForm p) (reflectedLevelLoop upper) ∧
      curveIntegral (graftedResolventForm p) (reflectedLevelLoop upper) = 2*(Real.pi : ℂ)*Complex.I := by
  have hleft (z : ℂ) (hz : z ∈ range (Path.segment a (star a))) :
      (-1 : ℂ)*(z-(p : ℂ)) ∈ Complex.slitPlane := by
    obtain ⟨s,rfl⟩ := hz
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [neg_one_mul,Complex.neg_re,Complex.sub_re,Complex.ofReal_re,
      Path.segment_apply,AffineMap.lineMap_apply_module,Complex.add_re,
      Complex.smul_re,smul_eq_mul,Complex.star_def,Complex.conj_re]
    nlinarith
  have hright (z : ℂ) (hz : z ∈ range (Path.segment (star b) b)) :
      (1 : ℂ)*(z-(p : ℂ)) ∈ Complex.slitPlane := by
    obtain ⟨s,rfl⟩ := hz
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [one_mul,Complex.sub_re,Complex.ofReal_re,
      Path.segment_apply,AffineMap.lineMap_apply_module,Complex.add_re,
      Complex.smul_re,smul_eq_mul,Complex.star_def,Complex.conj_re]
    nlinarith
  have hleft' := graftedResolvent_segment_log p (-1) (by norm_num) a (star a) hleft
  have hright' := graftedResolvent_segment_log p 1 one_ne_zero (star b) b hright
  simp only [neg_one_mul] at hleft'
  simp only [one_mul] at hright'
  have hbottom := graftedResolvent_curveIntegrable_conj p upper hupper.1
  have hA : a-(p : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using ha.ne'))
  have hB : b-(p : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using hb.ne'))
  have hlogA : star (Complex.log (a-(p : ℂ))) = Complex.log (star a-(p : ℂ)) := by
    simpa only [Complex.star_def,map_sub,Complex.conj_ofReal] using
      (Complex.log_conj (a-(p : ℂ)) (Complex.slitPlane_arg_ne_pi hA)).symm
  have hlogB : star (Complex.log (b-(p : ℂ))) = Complex.log (star b-(p : ℂ)) := by
    simpa only [Complex.star_def,map_sub,Complex.conj_ofReal] using
      (Complex.log_conj (b-(p : ℂ)) (Complex.slitPlane_arg_ne_pi hB)).symm
  constructor
  · exact hupper.1.symm.trans (hleft'.1.trans (hbottom.trans hright'.1))
  · unfold reflectedLevelLoop
    rw [curveIntegral_trans hupper.1.symm (hleft'.1.trans (hbottom.trans hright'.1)),
      curveIntegral_symm,curveIntegral_trans hleft'.1 (hbottom.trans hright'.1),
      curveIntegral_trans hbottom hright'.1,hupper.2,hleft'.2,hright'.2,
      graftedResolvent_curveIntegral_conj,hupper.2,star_sub,hlogA,hlogB]
    have hw : 0 < (a-(p : ℂ)).im := by simpa using ha
    have hj := graftedResolventLog_jump (a-(p : ℂ)) hw
    simp only [star_sub,Complex.star_def,Complex.conj_ofReal] at hj
    simp only [Complex.star_def]
    convert hj using 1
    ring

/-- The grafted level loop has resolvent integral `2πi` around every source point. -/
theorem nativeGraftedLevelLoop_resolvent {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀) (j : Fin N) :
    CurveIntegrable (graftedResolventForm (d j)) (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) ∧
      curveIntegral (graftedResolventForm (d j)) (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) =
        2*(Real.pi : ℂ)*Complex.I := by
  have hg := graftedCentralGeometry hN d t tmax eta x₀ ht htmax heta hheight
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcap : 0 < Real.sqrt t/(2*(N : ℝ)^2) := by positivity
  have hLa := hg.1
  have hbR := hg.2.2.2.1
  have hspL := (graftedLevelMeshSpacing_bounds _ _ _ hLa hcap).1
  have hspR := (graftedLevelMeshSpacing_bounds _ _ _ hbR hcap).1
  have hleft := (graftedLevelMesh_endpoint_re d t _ _ _ hLa hcap).1
  have hright := (graftedLevelMesh_endpoint_re d t _ _ _ hbR hcap).2
  have hd := graftedDeformationRadius_encloses d t ht j
  apply reflectedLevelLoop_resolvent
  · exact raisedLevelMeshVertex_im_pos hN d t _ _ ht hspL 0
  · exact raisedLevelMeshVertex_im_pos hN d t _ _ ht hspR _
  · simpa only [hleft] using hd.1
  · simpa only [hright] using hd.2
  · apply graftedLevelUpperPath_resolvent_log hN d t _ _ (d j) ht
      (le_trans hg.2.1.le hg.2.2.1.le)
    · intro k _
      exact raisedLevelMeshVertex_im_pos hN d t _ _ ht hspL k
    · intro k _
      exact raisedLevelMeshVertex_im_pos hN d t _ _ ht hspR k
    · intro x hx
      have hh := levelHeight_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight
        (hg.2.2.2.2 x hx)
      linarith

end BlockBand.GaussianBulk
