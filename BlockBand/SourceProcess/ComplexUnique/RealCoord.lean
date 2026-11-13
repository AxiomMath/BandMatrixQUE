module

public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramRealPath
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartLip
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem

/-!
# Real coordinates of a complex coordinate vector with a time coordinate

A finite family `κ` of complex coordinates `z : κ → ℂ` together with a time coordinate is
encoded as a real vector `y : Fin (rDim κ) → ℝ` (index `RIdx κ = Option (κ × Fin 2)`, `none` the
time, `some (p, r)` the real (`r = 0`) or imaginary (`r = 1`) part of `z_p`).
* `realDrift β`: time drift `1`, coordinate drifts `reIm r (β z p)`;
* `realCov Γ Γ'`: the real covariance of complex brackets `dz_p dz_q = Γ_pq`,
  `dz_p d\bar z_q = Γ'_pq` (`realCovEntry`), zero in the time row and column;
* `realSigma n`: rows `reIm r (n_a z p)` for complex noises `n_a`, zero time row;
  **`realSigma_cov`**: `σσᵀ = realCov` when `∑_a n_a n_a = Γ` and `∑_a n_a \bar n_a = Γ'`.
* `cC`, `cB`, `cB'`: the complex compensated coordinates and products along a real path, and
  `mpCompensated_some`, `mpBracket_some`: the real clauses are `reIm` of them, resp.
  `realCovL (cB) + realCovL' (cB')`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {κ : Type*} [Fintype κ]

/-- Real coordinate index: `none` is the time coordinate. -/
abbrev RIdx (κ : Type*) := Option (κ × Fin 2)

/-- The real dimension. -/
abbrev rDim (κ : Type*) [Fintype κ] : ℕ := Fintype.card (RIdx κ)

/-- Enumeration of the real coordinates. -/
def rEquiv (κ : Type*) [Fintype κ] : RIdx κ ≃ Fin (rDim κ) := Fintype.equivFin _

/-- Real coordinates of `(t, z)`. -/
def toR (t : ℝ) (z : κ → ℂ) : Fin (rDim κ) → ℝ := fun i =>
  ((rEquiv κ).symm i).elim t fun q => reIm q.2 (z q.1)

/-- The time coordinate. -/
def tOf (y : Fin (rDim κ) → ℝ) : ℝ := y (rEquiv κ none)

/-- The complex coordinates. -/
def zLin : (Fin (rDim κ) → ℝ) →ₗ[ℝ] (κ → ℂ) where
  toFun y p := (y (rEquiv κ (some (p, 0))) : ℂ) + (y (rEquiv κ (some (p, 1))) : ℂ) * Complex.I
  map_add' y y' := by funext p; simp only [Pi.add_apply, Complex.ofReal_add]; ring
  map_smul' r y := by
    funext p; simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]; ring

/-- The complex coordinates as a continuous linear map. -/
def zCLM : (Fin (rDim κ) → ℝ) →L[ℝ] (κ → ℂ) := LinearMap.toContinuousLinearMap zLin

/-- The complex coordinates. -/
def zOf (y : Fin (rDim κ) → ℝ) : κ → ℂ := zCLM y

theorem zOf_apply (y : Fin (rDim κ) → ℝ) (p : κ) :
    zOf y p = (y (rEquiv κ (some (p, 0))) : ℂ) + (y (rEquiv κ (some (p, 1))) : ℂ) * Complex.I :=
  rfl

theorem toR_some (t : ℝ) (z : κ → ℂ) (q : κ × Fin 2) :
    toR t z (rEquiv κ (some q)) = reIm q.2 (z q.1) := by
  simp [toR]

theorem tOf_toR (t : ℝ) (z : κ → ℂ) : tOf (toR t z) = t := by
  simp [tOf, toR]

theorem zOf_toR (t : ℝ) (z : κ → ℂ) : zOf (toR t z) = z := by
  funext p
  rw [zOf_apply, toR_some, toR_some]
  simp only [reIm]
  simp

theorem continuous_toR : Continuous fun x : ℝ × (κ → ℂ) => toR x.1 x.2 := by
  refine continuous_pi fun i => ?_
  unfold toR
  rcases ((rEquiv κ).symm i) with _ | q
  · exact continuous_fst
  · simp only [Option.elim_some, reIm]
    split_ifs
    · exact Complex.continuous_re.comp ((continuous_apply q.1).comp continuous_snd)
    · exact Complex.continuous_im.comp ((continuous_apply q.1).comp continuous_snd)

theorem continuous_zOf : Continuous (zOf (κ := κ)) := zCLM.continuous

theorem continuous_tOf : Continuous (tOf (κ := κ)) := continuous_apply _

/-- The real drift: `1` in time, `reIm r (β z p)` in coordinate `(p, r)`. -/
def realDrift (β : (κ → ℂ) → κ → ℂ) (y : Fin (rDim κ) → ℝ) : Fin (rDim κ) → ℝ := fun i =>
  ((rEquiv κ).symm i).elim 1 fun q => reIm q.2 (β (zOf y) q.1)

/-- The real covariance of the complex brackets `Γ` (bilinear) and `Γ'` (sesquilinear). -/
def realCov (Γ Γ' : (κ → ℂ) → κ → κ → ℂ) (y : Fin (rDim κ) → ℝ) :
    Matrix (Fin (rDim κ)) (Fin (rDim κ)) ℝ := fun i j =>
  ((rEquiv κ).symm i).elim 0 fun q => ((rEquiv κ).symm j).elim 0 fun q' =>
    realCovEntry q.2 q'.2 (Γ (zOf y) q.1 q'.1) (Γ' (zOf y) q.1 q'.1)

/-- The real diffusion matrix of complex noises `n_a(z)`. -/
def realSigma {ν : Type*} [Fintype ν] (n : ν → (κ → ℂ) → κ → ℂ) (y : Fin (rDim κ) → ℝ) :
    Matrix (Fin (rDim κ)) (Fin (Fintype.card ν)) ℝ := fun i k =>
  ((rEquiv κ).symm i).elim 0 fun q => reIm q.2 (n ((Fintype.equivFin ν).symm k) (zOf y) q.1)

/-- **`σσᵀ` is the real covariance** of matching complex brackets. -/
theorem realSigma_cov {ν : Type*} [Fintype ν] (n : ν → (κ → ℂ) → κ → ℂ)
    (Γ Γ' : (κ → ℂ) → κ → κ → ℂ) (y : Fin (rDim κ) → ℝ)
    (h : ∀ p q, ∑ a, n a (zOf y) p * n a (zOf y) q = Γ (zOf y) p q)
    (h' : ∀ p q, ∑ a, n a (zOf y) p * star (n a (zOf y) q) = Γ' (zOf y) p q) :
    realSigma n y * (realSigma n y).transpose = realCov Γ Γ' y := by
  ext i j
  rw [mul_apply]
  simp only [transpose_apply, realSigma, realCov]
  rcases ((rEquiv κ).symm i) with _ | q
  · simp
  rcases ((rEquiv κ).symm j) with _ | q'
  · simp
  simp only [Option.elim_some]
  rw [Equiv.sum_comp (Fintype.equivFin ν).symm (fun a => reIm q.2 (n a (zOf y) q.1) *
    reIm q'.2 (n a (zOf y) q'.1))]
  simp only [reIm_mul_reIm]
  rw [Finset.sum_add_distrib, ← map_sum, ← map_sum, h, h', realCovEntry_eq]

theorem lipschitzWith_reIm_apply (r : Fin 2) (p : κ) :
    LipschitzWith 1 fun z : κ → ℂ => reIm r (z p) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul]
  have e : reIm r (z p) - reIm r (z' p) = reIm r ((z - z') p) := by
    simp only [reIm, Pi.sub_apply]; split_ifs <;> simp
  rw [e]
  refine le_trans ?_ ((norm_le_pi_norm (z - z') p).trans_eq (dist_eq_norm z z').symm)
  unfold reIm; split_ifs
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

theorem locallyLipschitz_realDrift {β : (κ → ℂ) → κ → ℂ} (hβ : LocallyLipschitz β) :
    LocallyLipschitz (realDrift β) := by
  refine locallyLipschitz_pi fun i => ?_
  unfold realDrift
  rcases ((rEquiv κ).symm i) with _ | q
  · exact (LipschitzWith.const (1 : ℝ)).locallyLipschitz
  · exact (lipschitzWith_reIm_apply q.2 q.1).locallyLipschitz.comp
      (hβ.comp (zCLM (κ := κ)).lipschitzWith.locallyLipschitz)

theorem locallyLipschitz_realSigma {ν : Type*} [Fintype ν] {n : ν → (κ → ℂ) → κ → ℂ}
    (hn : ∀ a, LocallyLipschitz (n a)) : LocallyLipschitz (realSigma n) := by
  refine locallyLipschitz_matrix fun i k => ?_
  unfold realSigma
  rcases ((rEquiv κ).symm i) with _ | q
  · exact (LipschitzWith.const (0 : ℝ)).locallyLipschitz
  · exact (lipschitzWith_reIm_apply q.2 q.1).locallyLipschitz.comp
      ((hn _).comp (zCLM (κ := κ)).lipschitzWith.locallyLipschitz)

theorem continuous_realCov {Γ Γ' : (κ → ℂ) → κ → κ → ℂ} (hΓ : Continuous Γ)
    (hΓ' : Continuous Γ') : Continuous (realCov Γ Γ') := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold realCov
  rcases ((rEquiv κ).symm i) with _ | q
  · exact continuous_const
  rcases ((rEquiv κ).symm j) with _ | q'
  · exact continuous_const
  simp only [Option.elim_some, realCovEntry_eq]
  have h1 : Continuous fun y : Fin (rDim κ) → ℝ => Γ (zOf y) q.1 q'.1 :=
    (continuous_apply q'.1).comp ((continuous_apply q.1).comp (hΓ.comp continuous_zOf))
  have h2 : Continuous fun y : Fin (rDim κ) → ℝ => Γ' (zOf y) q.1 q'.1 :=
    (continuous_apply q'.1).comp ((continuous_apply q.1).comp (hΓ'.comp continuous_zOf))
  exact ((realCovL _ _).continuous.comp h1).add ((realCovL' _ _).continuous.comp h2)

/-!
### Complex compensated coordinates along a real path
-/

variable {Ω : Type*}

/-- Complex compensated coordinate `z_p(t) - z_p(0) - ∫_0^t β_p`. -/
def cC (β : (κ → ℂ) → κ → ℂ) (Y : ℝ≥0 → Ω → Fin (rDim κ) → ℝ) (p : κ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  zOf (Y t ω) p - zOf (Y 0 ω) p - ∫ s in Ioc (0 : ℝ) t, β (zOf (Y s.toNNReal ω)) p

/-- Complex compensated product `C_p C_q - ∫ Γ_pq`. -/
def cB (β : (κ → ℂ) → κ → ℂ) (Γ : (κ → ℂ) → κ → κ → ℂ) (Y : ℝ≥0 → Ω → Fin (rDim κ) → ℝ)
    (p q : κ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  cC β Y p t ω * cC β Y q t ω - ∫ s in Ioc (0 : ℝ) t, Γ (zOf (Y s.toNNReal ω)) p q

/-- Complex compensated sesquilinear product `C_p \bar C_q - ∫ Γ'_pq`. -/
def cB' (β : (κ → ℂ) → κ → ℂ) (Γ' : (κ → ℂ) → κ → κ → ℂ) (Y : ℝ≥0 → Ω → Fin (rDim κ) → ℝ)
    (p q : κ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  cC β Y p t ω * star (cC β Y q t ω) - ∫ s in Ioc (0 : ℝ) t, Γ' (zOf (Y s.toNNReal ω)) p q

variable {Y : ℝ≥0 → Ω → Fin (rDim κ) → ℝ} {ω : Ω}

theorem integrableOn_path {F : Type*} [NormedAddCommGroup F] {f : (Fin (rDim κ) → ℝ) → F}
    (hf : Continuous f) (hc : Continuous fun t => Y t ω) (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ => f (Y s.toNNReal ω)) (Ioc 0 t) :=
  integrableOn_Ioc_of_continuous (hf.comp hc) t

theorem realDrift_some (β : (κ → ℂ) → κ → ℂ) (y : Fin (rDim κ) → ℝ) (q : κ × Fin 2) :
    realDrift β y (rEquiv κ (some q)) = reIm q.2 (β (zOf y) q.1) := by
  simp [realDrift]

theorem realCov_some (Γ Γ' : (κ → ℂ) → κ → κ → ℂ) (y : Fin (rDim κ) → ℝ) (q q' : κ × Fin 2) :
    realCov Γ Γ' y (rEquiv κ (some q)) (rEquiv κ (some q')) =
      realCovL q.2 q'.2 (Γ (zOf y) q.1 q'.1) + realCovL' q.2 q'.2 (Γ' (zOf y) q.1 q'.1) := by
  simp [realCov, realCovEntry_eq]

theorem y_some (y : Fin (rDim κ) → ℝ) (q : κ × Fin 2) :
    y (rEquiv κ (some q)) = reIm q.2 (zOf y q.1) := by
  rcases q with ⟨p, r⟩
  rw [zOf_apply]
  fin_cases r <;> simp [reIm]

/-- The real compensated coordinate is `reIm` of the complex one. -/
theorem mpCompensated_some {β : (κ → ℂ) → κ → ℂ} (hβ : Continuous β)
    (hc : Continuous fun t => Y t ω) (q : κ × Fin 2) (t : ℝ≥0) :
    mpCompensated (realDrift β) Y (rEquiv κ (some q)) t ω = reIm q.2 (cC β Y q.1 t ω) := by
  have hint : Integrable (fun s : ℝ => β (zOf (Y s.toNNReal ω)) q.1) (volume.restrict (Ioc 0 t)) :=
    integrableOn_path ((continuous_apply q.1).comp (hβ.comp continuous_zOf)) hc t
  unfold mpCompensated cC
  simp only [realDrift_some]
  rw [y_some (Y t ω), y_some (Y 0 ω)]
  simp only [← reImCLM_apply]
  rw [(reImCLM q.2).integral_comp_comm hint, map_sub, map_sub]

/-- The real compensated products are `realCovL (cB) + realCovL' (cB')`. -/
theorem mpBracket_some {β : (κ → ℂ) → κ → ℂ} (hβ : Continuous β)
    {Γ Γ' : (κ → ℂ) → κ → κ → ℂ} (hΓ : Continuous Γ) (hΓ' : Continuous Γ')
    (hc : Continuous fun t => Y t ω) (q q' : κ × Fin 2) (t : ℝ≥0) :
    mpCompensated (realDrift β) Y (rEquiv κ (some q)) t ω *
        mpCompensated (realDrift β) Y (rEquiv κ (some q')) t ω -
        ∫ s in Ioc (0 : ℝ) t, realCov Γ Γ' (Y s.toNNReal ω) (rEquiv κ (some q)) (rEquiv κ (some q')) =
      realCovL q.2 q'.2 (cB β Γ Y q.1 q'.1 t ω) + realCovL' q.2 q'.2 (cB' β Γ' Y q.1 q'.1 t ω) := by
  have i1 : Integrable (fun s : ℝ => Γ (zOf (Y s.toNNReal ω)) q.1 q'.1)
      (volume.restrict (Ioc 0 t)) := integrableOn_path ((continuous_apply q'.1).comp
        ((continuous_apply q.1).comp (hΓ.comp continuous_zOf))) hc t
  have i2 : Integrable (fun s : ℝ => Γ' (zOf (Y s.toNNReal ω)) q.1 q'.1)
      (volume.restrict (Ioc 0 t)) := integrableOn_path ((continuous_apply q'.1).comp
        ((continuous_apply q.1).comp (hΓ'.comp continuous_zOf))) hc t
  simp only [realCov_some]
  rw [integral_add ((realCovL _ _).integrable_comp i1) ((realCovL' _ _).integrable_comp i2),
    (realCovL _ _).integral_comp_comm i1, (realCovL' _ _).integral_comp_comm i2,
    mpCompensated_some hβ hc q, mpCompensated_some hβ hc q', reIm_mul_reIm]
  unfold cB cB'
  rw [map_sub, map_sub]
  ring

theorem continuous_cC {β : (κ → ℂ) → κ → ℂ} (hβ : Continuous β) (hc : Continuous fun t => Y t ω)
    (p : κ) : Continuous fun t => cC β Y p t ω := by
  have hz : Continuous fun t => zOf (Y t ω) p := (continuous_apply p).comp (continuous_zOf.comp hc)
  have hi : Continuous fun u : ℝ≥0 => ∫ s in Ioc (0 : ℝ) u, β (zOf (Y s.toNNReal ω)) p := by
    have h1 := continuous_setIntegral_Ioc (g := fun u => (β (zOf (Y u ω)) p).re)
      fun t => integrableOn_path (f := fun y => (β (zOf y) p).re)
        (Complex.continuous_re.comp ((continuous_apply p).comp (hβ.comp continuous_zOf))) hc t
    have h2 := continuous_setIntegral_Ioc (g := fun u => (β (zOf (Y u ω)) p).im)
      fun t => integrableOn_path (f := fun y => (β (zOf y) p).im)
        (Complex.continuous_im.comp ((continuous_apply p).comp (hβ.comp continuous_zOf))) hc t
    have e : (fun u : ℝ≥0 => ∫ s in Ioc (0 : ℝ) u, β (zOf (Y s.toNNReal ω)) p) = fun u : ℝ≥0 =>
        ((∫ s in Ioc (0 : ℝ) u, (β (zOf (Y s.toNNReal ω)) p).re : ℝ) : ℂ) +
          ((∫ s in Ioc (0 : ℝ) u, (β (zOf (Y s.toNNReal ω)) p).im : ℝ) : ℂ) * Complex.I := by
      funext u
      have hint := integrableOn_path (f := fun y => β (zOf y) p)
        ((continuous_apply p).comp (hβ.comp continuous_zOf)) hc u
      rw [← Complex.re_add_im (∫ s in Ioc (0 : ℝ) u, β (zOf (Y s.toNNReal ω)) p),
        ← Complex.reCLM_apply, ← Complex.imCLM_apply, ← Complex.reCLM.integral_comp_comm hint,
        ← Complex.imCLM.integral_comp_comm hint]
      rfl
    rw [e]
    exact (Complex.continuous_ofReal.comp h1).add
      ((Complex.continuous_ofReal.comp h2).mul continuous_const)
  exact (hz.sub continuous_const).sub hi

end BlockBand.SourceProcess.ComplexUnique
