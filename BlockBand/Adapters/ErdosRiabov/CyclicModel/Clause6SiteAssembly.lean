module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause6EndpointControl
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ScalarProfileSourceFaithfulNormalization
public import Mathlib

/-!
# Site-level assembly for ER Definition 2.4(vi)

This module tensors the cyclic neighboring-entry estimate to physical sites
and assembles the short- and long-separation branches in the normalization
supplied by the fixed-bond Fourier proof.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.4(vi), and Proposition 2.8(i), specifically
the neighboring-entry/telescoping argument after (2.26).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6SiteAssembly

open ERFourierInverse ERFourierAlgebra ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERClause1 ERHerglotz ERScalarProfileControl ERScalarProfileSourceFaithfulNormalization ERPhysicalBridge ERClause6CyclicDifference ERClause6EndpointControl

local instance (p : Params) : NeZero p.n := p.nNeZero

lemma sourceFaithfulDecay_le_half (p : Params) :
    sourceFaithfulDecay p ≤ 1 / 2 := by
  unfold sourceFaithfulDecay clause1Decay
  exact min_le_left _ _

/-- The two cyclic paths are unchanged when the endpoints are exchanged. -/
lemma cyclicTwoPathNumerator_oriented_comm (p : Params) (ρ : ℂ)
    (x y : ZMod p.n) :
    cyclicTwoPathNumerator p ρ (orientedBlockDistance p x y) =
      cyclicTwoPathNumerator p ρ (orientedBlockDistance p y x) := by
  by_cases hxy : x = y
  · subst y
    rfl
  · have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    let _ : NeZero (x - y) := ⟨hne⟩
    have hrev : y - x = -(x - y) := by ring
    have hdlt : (x - y).val < p.n := ZMod.val_lt _
    unfold orientedBlockDistance
    rw [hrev, ZMod.val_neg_of_ne_zero (x - y)]
    unfold cyclicTwoPathNumerator
    have hback : p.n - (p.n - (x - y).val) = (x - y).val := by omega
    rw [hback]
    ring

/-- Symmetry of the concrete cyclic Fourier Green kernel. -/
theorem fourierGreenKernel_comm (p : Params) {α : ℂ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1) (x y : ZMod p.n) :
    fourierGreenKernel p α x y = fourierGreenKernel p α y x := by
  rw [fourierGreenKernel_eq_cyclicResolventCandidate p hα0 hα,
    fourierGreenKernel_eq_cyclicResolventCandidate p hα0 hα]
  unfold cyclicResolventCandidate cyclicTwoPathKernel
  rw [cyclicTwoPathNumerator_oriented_comm p
    (contractingRecurrenceRoot p α) x y]

/-- The cyclic distance chooses one of the two directed paths, and that path
really reaches the opposite endpoint in `ZMod n`. -/
theorem exists_shorter_oriented_path (p : Params) (b c : ZMod p.n) :
    let r := cyclicBlockDistance p b c
    (c = b + (r : ℕ)) ∨ (b = c + (r : ℕ)) := by
  dsimp only
  let d := orientedBlockDistance p c b
  have hdlt : d < p.n := by
    dsimp [d, orientedBlockDistance]
    exact ZMod.val_lt _
  have hdle : d ≤ p.n := hdlt.le
  have hdcast : ((d : ℕ) : ZMod p.n) = c - b := by
    dsimp [d, orientedBlockDistance]
    exact ZMod.natCast_zmod_val (c - b)
  have hbackcast : ((p.n - d : ℕ) : ZMod p.n) = b - c := by
    rw [Nat.cast_sub hdle]
    simp [hdcast]
  rw [cyclicBlockDistance_comm p b c]
  unfold cyclicBlockDistance
  change (c = b + (min d (p.n - d) : ℕ)) ∨
    (b = c + (min d (p.n - d) : ℕ))
  rcases le_total d (p.n - d) with h | h
  · left
    rw [min_eq_left h, hdcast]
    ring
  · right
    rw [min_eq_right h, hbackcast]
    ring

/-- Short-path Green control for arbitrary endpoints, after choosing the
shorter of the two cyclic orientations. -/
theorem norm_alpha_mul_fourierGreenKernel_sub_le_shorter_endpoints
    (p : Params) {α : ℂ} {η : ℝ}
    (hα0 : α ≠ 0) (hα : ‖α‖ < 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (hmargin : η / 4 ≤ 1 - ‖α‖)
    (a b c : ZMod p.n)
    (hshort : (Real.sqrt η / 2) * cyclicBlockDistance p b c ≤ 1) :
    ‖α * (fourierGreenKernel p α a b -
      fourierGreenKernel p α a c)‖ ≤
      (2 * Real.exp 2 /
        (Real.sqrt (p.b * jumpBondMargin p) * fixedWrapFloor)) *
        cyclicBlockDistance p b c *
        (Real.exp (-(Real.sqrt η / 2) * cyclicBlockDistance p a b) +
          Real.exp (-(Real.sqrt η / 2) *
            cyclicBlockDistance p a c)) := by
  let r := cyclicBlockDistance p b c
  rcases exists_shorter_oriented_path p b c with hbc | hcb
  · have hpath :=
      norm_alpha_mul_fourierGreenKernel_path_sub_le_endpoints
        p hα0 hα hη0 hη1 hthreshold hmargin b a r hshort
    rw [fourierGreenKernel_comm p hα0 hα b a,
      fourierGreenKernel_comm p hα0 hα (b + r) a] at hpath
    rw [← hbc] at hpath
    rw [cyclicBlockDistance_comm p b a,
      cyclicBlockDistance_comm p c a] at hpath
    simpa [r, norm_neg, show
      α * (fourierGreenKernel p α a b - fourierGreenKernel p α a c) =
        -(α * (fourierGreenKernel p α a c -
          fourierGreenKernel p α a b)) by ring] using hpath
  · have hpath :=
      norm_alpha_mul_fourierGreenKernel_path_sub_le_endpoints
        p hα0 hα hη0 hη1 hthreshold hmargin c a r hshort
    rw [fourierGreenKernel_comm p hα0 hα c a,
      fourierGreenKernel_comm p hα0 hα (c + r) a] at hpath
    rw [← hcb] at hpath
    rw [cyclicBlockDistance_comm p c a,
      cyclicBlockDistance_comm p b a] at hpath
    simpa [r, add_comm] using hpath

/-- Above the clause-(vi) threshold the localization length is on its
square-root branch. -/
theorem erLocalizationLength_eq_width_div_sqrt_of_threshold
    (p : Params) {η : ℝ} (hη0 : 0 < η)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η) :
    erLocalizationLength p η = (p.W : ℝ) / Real.sqrt η := by
  unfold erLocalizationLength
  apply min_eq_left
  have hn0 : 0 < (p.n : ℝ) := by exact_mod_cast p.n_pos
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hs : 1 / (p.n : ℝ) ≤ Real.sqrt η := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / (p.n : ℝ))]
    exact Real.sqrt_le_sqrt hthreshold
  rw [show (p.L : ℝ) = (p.n : ℝ) * (p.W : ℝ) by
    simp [Conventions.ModelParameters.L, Conventions.dimension]]
  apply (div_le_iff₀ hs0).2
  have hone : 1 ≤ (p.n : ℝ) * Real.sqrt η := by
    have := mul_le_mul_of_nonneg_left hs hn0.le
    field_simp at this
    exact this
  nlinarith [p.real_W_pos]

/-- The block-path length has exactly the scaling needed by the source
Lipschitz factor once `ℓ = W / √η`. -/
lemma blockDistance_div_width_le_siteFactor
    (p : Params) {η : ℝ} (hη0 : 0 < η)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (b c : Site p.n p.W) :
    (cyclicBlockDistance p b.1 c.1 : ℝ) / p.W ≤
      ((erSiteDistance p b c : ℝ) + p.W) /
        (erLocalizationLength p η ^ 2 * η) := by
  have hW0 : 0 < (p.W : ℝ) := p.real_W_pos
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hsquare : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt hη0.le
  have hdist := width_mul_cyclicBlockDistance_le_siteDistance_add_width p b c
  have hdistR : (p.W : ℝ) * cyclicBlockDistance p b.1 c.1 ≤
      (erSiteDistance p b c : ℝ) + p.W := by exact_mod_cast hdist
  rw [erLocalizationLength_eq_width_div_sqrt_of_threshold p hη0 hthreshold]
  field_simp [ne_of_gt hW0, ne_of_gt hs0, ne_of_gt hη0]
  nlinarith

/-- On the near branch the shorter block path lies in the scalar
telescoping regime. -/
lemma shorter_path_is_scalar_short
    (p : Params) {η : ℝ} (hη0 : 0 < η)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (b c : Site p.n p.W)
    (hnear : (erSiteDistance p b c : ℝ) + p.W <
      erLocalizationLength p η) :
    (Real.sqrt η / 2) * cyclicBlockDistance p b.1 c.1 ≤ 1 := by
  have hW0 : 0 < (p.W : ℝ) := p.real_W_pos
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hdist := width_mul_cyclicBlockDistance_le_siteDistance_add_width p b c
  have hdistR : (p.W : ℝ) * cyclicBlockDistance p b.1 c.1 ≤
      (erSiteDistance p b c : ℝ) + p.W := by exact_mod_cast hdist
  rw [erLocalizationLength_eq_width_div_sqrt_of_threshold p hη0 hthreshold]
    at hnear
  have hscaled := lt_of_le_of_lt hdistR hnear
  have hr : (cyclicBlockDistance p b.1 c.1 : ℝ) <
      1 / Real.sqrt η := by
    calc
      (cyclicBlockDistance p b.1 c.1 : ℝ) =
          ((p.W : ℝ) * cyclicBlockDistance p b.1 c.1) / p.W := by
            field_simp
      _ < ((p.W : ℝ) / Real.sqrt η) / p.W :=
        div_lt_div_of_pos_right hscaled hW0
      _ = 1 / Real.sqrt η := by field_simp
  have hrs := mul_lt_mul_of_pos_left hr hs0
  have hinv : Real.sqrt η * (1 / Real.sqrt η) = 1 := by
    field_simp
  rw [hinv] at hrs
  nlinarith

/-- At equal blocks, the exponential branch of the source control is large
enough to absorb one tensor correction after multiplication by the `+W`
Lipschitz allowance. -/
lemma one_div_width_le_exp_half_mul_siteFactor_control_of_sameBlock
    (p : Params) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (a q b c : Site p.n p.W) (haq : a.1 = q.1) :
    1 / (p.W : ℝ) ≤
      Real.exp (1 / 2) *
        (((erSiteDistance p b c : ℝ) + p.W) /
          erLocalizationLength p η) *
        erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a q := by
  let ell := erLocalizationLength p η
  have hW0 : 0 < (p.W : ℝ) := p.real_W_pos
  have hell0 : 0 < ell := by
    dsimp [ell]
    unfold erLocalizationLength
    exact lt_min (div_pos hW0 (Real.sqrt_pos.2 hη0)) p.real_L_pos
  have hell : ell = (p.W : ℝ) / Real.sqrt η :=
    erLocalizationLength_eq_width_div_sqrt_of_threshold p hη0 hthreshold
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.2 hη0
  have hs1 : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη1
  have hdistNat := siteDistance_le_width_mul_cyclicBlockDistance_add_width p a q
  have hblock0 : cyclicBlockDistance p a.1 q.1 = 0 := by
    rw [haq]
    simp [cyclicBlockDistance, orientedBlockDistance]
  rw [hblock0, mul_zero, zero_add] at hdistNat
  have hdist : (erSiteDistance p a q : ℝ) ≤ p.W := by exact_mod_cast hdistNat
  have ha0 : 0 ≤ sourceFaithfulDecay p := (sourceFaithfulDecay_pos p).le
  have ha1 := sourceFaithfulDecay_le_half p
  have hratio : (p.W : ℝ) / ell = Real.sqrt η := by
    rw [hell]
    field_simp
  have hexponent :
      sourceFaithfulDecay p * (erSiteDistance p a q : ℝ) / ell ≤ 1 / 2 := by
    have hmul := mul_le_mul ha1 hdist (by positivity) (by norm_num)
    calc
      sourceFaithfulDecay p * (erSiteDistance p a q : ℝ) / ell ≤
          ((1 / 2) * (p.W : ℝ)) / ell :=
        div_le_div_of_nonneg_right hmul hell0.le
      _ = (1 / 2) * Real.sqrt η := by rw [← hratio]; ring
      _ ≤ 1 / 2 := by nlinarith
  have hexp :
      Real.exp (-(1 / 2)) ≤
        Real.exp (-sourceFaithfulDecay p *
          (erSiteDistance p a q : ℝ) / ell) :=
    Real.exp_le_exp.mpr (by
      have hneg := neg_le_neg hexponent
      simpa only [neg_div, neg_mul] using hneg)
  have hcontrol := exp_branch_le_erManuscriptCyclicControl p hη0
    (sourceFaithfulDecay p) a q
  have hbase :
      (1 / (ell * η)) * Real.exp (-(1 / 2)) ≤
        erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a q := by
    exact (mul_le_mul_of_nonneg_left hexp
      (one_div_nonneg.mpr (mul_nonneg hell0.le hη0.le))).trans
      (by simpa [ell] using hcontrol)
  have hs : (p.W : ℝ) ≤ (erSiteDistance p b c : ℝ) + p.W := by
    linarith [Nat.cast_nonneg (α := ℝ) (erSiteDistance p b c)]
  calc
    1 / (p.W : ℝ) =
        Real.exp (1 / 2) *
          (((p.W : ℝ) / ell) *
            ((1 / (ell * η)) * Real.exp (-(1 / 2)))) := by
      rw [hell, show Real.exp (-(1 / 2)) =
        1 / Real.exp (1 / 2) by simp [Real.exp_neg, one_div]]
      field_simp [ne_of_gt hW0, ne_of_gt hs0, ne_of_gt hη0,
        ne_of_gt (Real.exp_pos (1 / 2))]
      nlinarith [Real.sq_sqrt hη0.le]
    _ ≤ Real.exp (1 / 2) *
        ((((erSiteDistance p b c : ℝ) + p.W) / ell) *
          ((1 / (ell * η)) * Real.exp (-(1 / 2)))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right hs hell0.le
    _ ≤ Real.exp (1 / 2) *
        ((((erSiteDistance p b c : ℝ) + p.W) / ell) *
          erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a q) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = Real.exp (1 / 2) *
        (((erSiteDistance p b c : ℝ) + p.W) / ell) *
          erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a q := by ring

/-- The block-supported `-I ⊗ J_W` difference is absorbed by the `+W`
allowance in the source Lipschitz factor. -/
theorem blockCorrection_div_width_le_sourceFaithful
    (p : Params) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hthreshold : (1 / (p.n : ℝ)) ^ 2 ≤ η)
    (a b c : Site p.n p.W) :
    ‖(if a.1 = b.1 then (1 : ℂ) else 0) -
        (if a.1 = c.1 then (1 : ℂ) else 0)‖ / (p.W : ℝ) ≤
      Real.exp (1 / 2) *
        (((erSiteDistance p b c : ℝ) + p.W) /
          erLocalizationLength p η) *
        (erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a b +
          erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a c) := by
  have hell0 : 0 < erLocalizationLength p η := by
    unfold erLocalizationLength
    exact lt_min (div_pos p.real_W_pos (Real.sqrt_pos.2 hη0)) p.real_L_pos
  have hpref0 : 0 ≤ Real.exp (1 / 2) *
      (((erSiteDistance p b c : ℝ) + p.W) /
        erLocalizationLength p η) := by positivity
  have hb0 := erManuscriptCyclicControl_nonneg p
    (sourceFaithfulDecay p) 8 η hη0 a b
  have hc0 := erManuscriptCyclicControl_nonneg p
    (sourceFaithfulDecay p) 8 η hη0 a c
  by_cases hab : a.1 = b.1 <;> by_cases hac : a.1 = c.1
  · have hbc : b.1 = c.1 := hab.symm.trans hac
    simp only [hab, hbc, ite_true, sub_self, norm_zero, zero_div]
    exact mul_nonneg hpref0 (add_nonneg hb0 hc0)
  · have hb :=
      one_div_width_le_exp_half_mul_siteFactor_control_of_sameBlock
        p hη0 hη1 hthreshold a b b c hab
    have hbc : b.1 ≠ c.1 := by
      intro h
      exact hac (hab.trans h)
    simp only [hab, hbc, ite_true, ite_false, sub_zero, norm_one]
    calc
      1 / (p.W : ℝ) ≤ Real.exp (1 / 2) *
          (((erSiteDistance p b c : ℝ) + p.W) /
            erLocalizationLength p η) *
          erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a b := hb
      _ ≤ Real.exp (1 / 2) *
          (((erSiteDistance p b c : ℝ) + p.W) /
            erLocalizationLength p η) *
          (erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a b +
            erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a c) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_right hc0
        · exact hpref0
  · have hc :=
      one_div_width_le_exp_half_mul_siteFactor_control_of_sameBlock
        p hη0 hη1 hthreshold a c b c hac
    have hcb : c.1 ≠ b.1 := by
      intro h
      exact hab (hac.trans h)
    simp only [hac, hcb, ite_true, ite_false, zero_sub, norm_neg, norm_one]
    calc
      1 / (p.W : ℝ) ≤ Real.exp (1 / 2) *
          (((erSiteDistance p b c : ℝ) + p.W) /
            erLocalizationLength p η) *
          erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a c := hc
      _ ≤ Real.exp (1 / 2) *
          (((erSiteDistance p b c : ℝ) + p.W) /
            erLocalizationLength p η) *
          (erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a b +
            erManuscriptCyclicControl p (sourceFaithfulDecay p) 8 η a c) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_left hb0
        · exact hpref0
  · simp only [hab, hac, ite_false, sub_self, norm_zero, zero_div]
    exact mul_nonneg hpref0 (add_nonneg hb0 hc0)

/-- Exact tensor identity for a difference in the second site variable.  It
exhibits separately the cyclic Green difference and the block-supported
`-I ⊗ J_W` correction. -/
theorem erTheta_sub_eq_green_sub_blockCorrection_div_width
    (p : Params) {z₁ z₂ : ℂ}
    (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (a b c : Site p.n p.W) :
    erTheta p z₁ z₂ a b - erTheta p z₁ z₂ a c =
      ((fourierGreenKernel p
          (erSemicircleStieltjes z₁ *
            starRingEnd ℂ (erSemicircleStieltjes z₂)) a.1 b.1 -
          (if a.1 = b.1 then 1 else 0)) -
        (fourierGreenKernel p
          (erSemicircleStieltjes z₁ *
            starRingEnd ℂ (erSemicircleStieltjes z₂)) a.1 c.1 -
          (if a.1 = c.1 then 1 else 0))) / (p.W : ℂ) := by
  rw [erTheta_apply_eq_siteGreenKernel_sub_identity p hz₁ hz₂ a b,
    erTheta_apply_eq_siteGreenKernel_sub_identity p hz₁ hz₂ a c]
  unfold siteGreenKernel
  field_simp
  ring

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERClause6SiteAssembly
