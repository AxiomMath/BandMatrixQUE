module

public import BlockBand.Endpoints.Normalization.LeadGaussianBlock

/-!
# The physical lead-profile theorem, pointwise: field identification and block-0 removal

**Main result** (`leadRecon_deletion_pointwise`, deterministic). For every `Φ ∈ C_b(𝒫(𝕋))` and `ε > 0` there is `C ≥ 0` such that for every
admissible `p`, `|e| < 2`, every lead sample `x = (path, layer)` with `IsLeadRegular p 0 e x`
and every nonzero block vector `g`, with `ω = leadExterior p 0 x`, `M = blockFieldFactor ω e`,
`h = Lg` (`commonPortProbe`, `g` read on the common port):

`|n⁻¹ Σ_{s ∈ ℤ/n} Φ(ℛ_{s/n} ν(p(Mg, e))) - n⁻¹ Σ_{J<n} Φ(leadProfile b e n W path h J)|
   ≤ ε + C · p_0(Mg, e)`,

where the left profile is the full-ring profile of the Gaussian field (block `0` included) and
`p_0(Mg, e)` its block-`0` mass fraction. Proof: `leadField_identity` gives the block masses
`m_j = c · leadPositionMass(pos j)` for `j ≠ 0` (`pos` = the lead position of ring block `j`,
`leadBlockPos`, a bijection onto `Fin (n-3) ⊕ Fin 2` with `leadRingBlock ∘ pos = val`); hence the
rotated lead profile at `J = s` is the renormalized deleted profile; `abs_profile_deleted_sub_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.Critical
open scoped ComplexConjugate ComplexOrder BoundedContinuousFunction

section Positions

variable (p : Parameters)

/-- The lead position of ring block `j` (block `0` removed): block `1` is the near port, block
`n-1` the far port, block `2 + i` path position `i`. -/
def leadBlockPos (j : ZMod p.n) : Fin (p.n - 3) ⊕ Fin 2 :=
  if j.val = 1 then Sum.inr 0
  else if j.val = p.n - 1 then Sum.inr 1
  else Sum.inl ⟨min (j.val - 2) (p.n - 3 - 1), by have := p.n_ge_four; omega⟩

/-- The site of position `x` with in-block coordinate `a`. -/
def posSite {r W : ℕ} (x : Fin r ⊕ Fin 2) (a : Fin W) : FullSite W r :=
  Sum.elim (fun i => Sum.inl (i, a)) (fun t => Sum.inr (t, a)) x

theorem leadPos_eq_posSite (y : OffBlockSite p 0) :
    leadPos p 0 y = posSite (leadBlockPos p y.1.1) y.1.2 := by
  unfold leadPos leadBlockPos posSite
  simp only [sub_zero]
  split_ifs <;> rfl

theorem leadPositionMass_eq_posSite (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (x : Fin r ⊕ Fin 2) :
    leadPositionMass b e W r ω h x =
      ∑ a : Fin W, ‖(leadResponse b e W r ω *ᵥ h) (posSite x a)‖ ^ 2 := by
  cases x <;> rfl

theorem leadRingBlock_leadBlockPos (j : ZMod p.n) (hj : j ≠ 0) :
    leadRingBlock (p.n - 3) (leadBlockPos p j) = j.val := by
  have h4 := p.n_ge_four
  have hlt := ZMod.val_lt j
  have h0 : j.val ≠ 0 := fun h => hj ((ZMod.val_eq_zero j).mp h)
  unfold leadBlockPos
  by_cases h1 : j.val = 1
  · simp only [h1, ↓reduceIte, leadRingBlock]
  · by_cases h2 : j.val = p.n - 1
    · have hn2 : p.n ≠ 2 := by omega
      simp [h2, hn2, leadRingBlock]
      omega
    · simp only [h1, h2, ↓reduceIte, leadRingBlock]
      omega

theorem leadBlockPos_injective :
    Function.Injective fun j : {j : ZMod p.n // j ≠ 0} => leadBlockPos p j.1 := by
  intro j j' h
  have h1 := leadRingBlock_leadBlockPos p j.1 j.2
  have h2 := leadRingBlock_leadBlockPos p j'.1 j'.2
  simp only at h
  rw [h] at h1
  exact Subtype.ext (ZMod.val_injective p.n (h1.symm.trans h2))

theorem card_ne_zero_zmod :
    Fintype.card {j : ZMod p.n // j ≠ 0} = Fintype.card (Fin (p.n - 3) ⊕ Fin 2) := by
  have h4 := p.n_ge_four
  rw [Fintype.card_subtype_compl, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    ZMod.card, Fintype.card_subtype_eq]
  omega

/-- `leadBlockPos` as an equivalence `{j ≠ 0} ≃ Fin (n-3) ⊕ Fin 2`. -/
def leadBlockPosEquiv : {j : ZMod p.n // j ≠ 0} ≃ Fin (p.n - 3) ⊕ Fin 2 :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨leadBlockPos_injective p, card_ne_zero_zmod p⟩)

/-- Sums over lead positions are sums over the ring blocks `j ≠ 0`. -/
theorem sum_leadPositions {M : Type*} [AddCommMonoid M] (F : Fin (p.n - 3) ⊕ Fin 2 → M) :
    ∑ x, F x = ∑ j : ZMod p.n, if j = 0 then 0 else F (leadBlockPos p j) := by
  rw [← (leadBlockPosEquiv p).sum_comp F]
  have h1 : ∀ j : ZMod p.n, (if j = 0 then 0 else F (leadBlockPos p j)) =
      if j ≠ 0 then F (leadBlockPos p j) else 0 := fun j => by
    by_cases hj : j = 0 <;> simp [hj]
  simp_rw [h1]
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun j : ZMod p.n => j ≠ 0) _
    (fun j => by simp)]
  rfl

theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ s : ZMod p.n, f s.val = ∑ J ∈ Finset.range p.n, f J := by
  refine Finset.sum_bij (fun s _ => s.val) (fun s _ => Finset.mem_range.mpr (ZMod.val_lt s))
    (fun s _ t _ h => ZMod.val_injective p.n h) (fun J hJ => ?_) (fun s _ => rfl)
  exact ⟨(J : ZMod p.n), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.mp hJ)⟩

end Positions

section Profiles

variable (p : Parameters)

theorem blockLift_smul {k : ZMod p.n} (ω : BlockState p k) (e : ℝ) (a : ℂ)
    (v : BlockSite p k → ℂ) : blockLift p k ω e (a • v) = a • blockLift p k ω e v := by
  rw [← liftMatrix_mulVec, ← liftMatrix_mulVec, mulVec_smul]

theorem map_finsetSum_measure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) {ι : Type*} (s : Finset ι) (μ : ι → Measure α) :
    Measure.map f (∑ i ∈ s, μ i) = ∑ i ∈ s, Measure.map f (μ i) := by
  simp only [← Measure.mapₗ_apply_of_measurable hf, map_sum]

theorem coe_dite_pos {P : Prop} [Decidable P] (hP : P) (a : P → MassProfile)
    (b : ¬P → MassProfile) :
    ((if h : P then a h else b h : MassProfile) : Measure Torus) = (a hP : Measure Torus) := by
  simp [hP]

/-- The lead profile as a measure, when the total lead mass is positive. -/
theorem coe_leadProfile_of (b e : ℝ) (n W : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ)
    (J : ℕ) (hpos : 0 < ∑ x, leadPositionMass b e W (n - 3) ω h x) :
    (leadProfile b e n W ω h J : Measure Torus) =
      ∑ x, ENNReal.ofReal (leadPositionMass b e W (n - 3) ω h x /
          ∑ x', leadPositionMass b e W (n - 3) ω h x') •
        Measure.dirac (QuotientAddGroup.mk ((((leadRingBlock (n - 3) x + J) % n : ℕ) : ℝ) / n) :
          Torus) := by
  have hnn : ∀ x, 0 ≤ leadPositionMass b e W (n - 3) ω h x := fun x => by
    rw [leadPositionMass_eq_posSite]; positivity
  have hprob : IsProbabilityMeasure (∑ x, ENNReal.ofReal (leadPositionMass b e W (n - 3) ω h x /
      ∑ x', leadPositionMass b e W (n - 3) ω h x') •
        Measure.dirac (QuotientAddGroup.mk ((((leadRingBlock (n - 3) x + J) % n : ℕ) : ℝ) / n) :
          Torus)) := by
    constructor
    simp only [Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => div_nonneg (hnn x) hpos.le), ← Finset.sum_div,
      div_self hpos.ne', ENNReal.ofReal_one]
  unfold leadProfile
  classical
  exact coe_dite_pos hprob _ _

/-- The rotated profile of a nonnegative mass vector of total one, as a measure. -/
theorem coe_rotation_massVectorProfile (q : ZMod p.n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hsum : ∑ j, q j = 1) (s : ZMod p.n) :
    (massProfileRotation (physicalProfileGrid p s) (massVectorProfile p q) : Measure Torus) =
      ∑ j, ENNReal.ofReal (q j) • Measure.dirac (physicalProfileGrid p (j + s)) := by
  have hprob : IsProbabilityMeasure (massVectorMeasure p q) := by
    constructor
    unfold massVectorMeasure
    simp only [Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq j), hsum, ENNReal.ofReal_one]
  change Measure.map (Homeomorph.addLeft (physicalProfileGrid p s))
    (massVectorProfile p q : Measure Torus) = _
  rw [coe_massVectorProfile_of p q hprob]
  unfold massVectorMeasure
  have hm : Measurable (Homeomorph.addLeft (physicalProfileGrid p s)) :=
    (Homeomorph.addLeft _).continuous.measurable
  rw [map_finsetSum_measure hm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.map_smul _ hm.aemeasurable, Measure.map_dirac' hm,
    BlockBand.QUE.Invariance.physicalProfileGrid_add, add_comm]
  rfl

end Profiles

section Pointwise

theorem sum_ite_zero_eq {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    ∑ j : ZMod n, (if j = 0 then 0 else f j) = ∑ j, f j - f 0 := by
  have : ∀ j : ZMod n, (if j = 0 then 0 else f j) = f j - (if j = 0 then f j else 0) := fun j => by
    by_cases hj : j = 0 <;> simp [hj]
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

variable (p : Parameters)

/-- Block masses of the Gaussian field: `m_j = c · leadPositionMass (pos j)` for `j ≠ 0`. -/
theorem blockForm_fieldFactor_eq (e : ℝ) (x : GrowthPath p.W × LayerSample p.W .common)
    (hreg : IsLeadRegular p 0 e x) (g : BlockSite p 0 → ℂ) (j : ZMod p.n) (hj : j ≠ 0) :
    quadForm (blockForm p 0 (leadExterior p 0 x) e j)
        (blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g) =
      p.c * leadPositionMass p.b e p.W (p.n - 3) x.1
        (commonPortProbe p.b e (leadSchur e p.W (p.n - 3) x.1) (x.2, blockPortVector p 0 g))
        (leadBlockPos p j) := by
  have hc : 0 ≤ p.c := by have := p.b_lt_half; unfold Parameters.c; linarith
  rw [quadForm_blockForm, leadPositionMass_eq_posSite, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfac : blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g =
      ((Real.sqrt p.c : ℝ) : ℂ) • ((blockShifted p 0 (leadExterior p 0 x) e)⁻¹ *ᵥ g) := by
    unfold blockFieldFactor; rw [smul_mulVec]
  rw [hfac, blockLift_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    leadField_identity p 0 e x hreg g (j, a)]
  have hj' : ¬ ((j, a) : p.Site).1 = 0 := hj
  simp only [hj', ↓reduceDIte]
  rw [leadPos_eq_posSite, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt hc]
  congr 3
  unfold commonPortProbe
  rw [mulVec_mulVec]

theorem quadForm_blockForm_zero_fieldFactor_pos (e : ℝ)
    (x : GrowthPath p.W × LayerSample p.W .common) (hreg : IsLeadRegular p 0 e x)
    (g : BlockSite p 0 → ℂ) (hg : g ≠ 0) :
    0 < quadForm (blockForm p 0 (leadExterior p 0 x) e 0)
      (blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g) := by
  rw [blockForm_self]
  set v := blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g
  have hv : v ≠ 0 := by
    intro hv0
    have hdet : (blockShifted p 0 (leadExterior p 0 x) e).det ≠ 0 := hreg.2.2.2.1
    have hc : 0 < p.c := by have := p.b_lt_half; unfold Parameters.c; linarith
    have hsq : ((Real.sqrt p.c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
    apply hg
    have h1 : (blockShifted p 0 (leadExterior p 0 x) e)⁻¹ *ᵥ g = 0 := by
      have : ((Real.sqrt p.c : ℝ) : ℂ) • ((blockShifted p 0 (leadExterior p 0 x) e)⁻¹ *ᵥ g) = 0 := by
        rw [← hv0]; unfold v blockFieldFactor; rw [smul_mulVec]
      exact (smul_eq_zero.mp this).resolve_left hsq
    have h2 := congrArg (fun u => blockShifted p 0 (leadExterior p 0 x) e *ᵥ u) h1
    simp only [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec,
      mulVec_zero] at h2
    exact h2
  unfold quadForm
  rw [one_mulVec, re_star_dotProduct_self]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun j _ => by positivity)
    (Finset.mem_univ i))

/-- **Pointwise field identification and removal of block `0`.** See the module docstring.
-/
theorem leadRecon_deletion_pointwise (Φ : MassProfile →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Parameters) (e : ℝ), |e| < 2 →
    ∀ (x : GrowthPath p.W × LayerSample p.W .common), IsLeadRegular p 0 e x →
    ∀ g : BlockSite p 0 → ℂ, g ≠ 0 →
      |leadReconObservable p Φ 0 (leadExterior p 0 x) e
            (blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g) -
          (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n, Φ (leadProfile p.b e p.n p.W x.1
            (commonPortProbe p.b e (leadSchur e p.W (p.n - 3) x.1) (x.2, blockPortVector p 0 g))
            J)| ≤
        ε + C * blockReconMass p 0 (leadExterior p 0 x) e
          (blockFieldFactor p 0 (leadExterior p 0 x) e *ᵥ g) 0 := by
  obtain ⟨C₀, hC₀, hdel⟩ := abs_profile_deleted_sub_le Φ ε hε
  refine ⟨2 * max C₀ ‖Φ‖, by positivity, ?_⟩
  intro p e he x hreg g hg
  set ω := leadExterior p 0 x
  set v := blockFieldFactor p 0 ω e *ᵥ g
  set h := commonPortProbe p.b e (leadSchur e p.W (p.n - 3) x.1) (x.2, blockPortVector p 0 g)
  set lpm := leadPositionMass p.b e p.W (p.n - 3) x.1 h
  set m : ZMod p.n → ℝ := fun j => quadForm (blockForm p 0 ω e j) v
  have hm0 : ∀ j, 0 ≤ m j := fun j => quadForm_blockForm_nonneg p 0 ω e j v
  have hS : ∑ j, m j = quadForm (clockForm p 0 ω e) v := sum_quadForm_blockForm p 0 ω e v
  have hrecon : ∀ j, blockReconMass p 0 ω e v j = m j / ∑ j', m j' := fun j => by
    rw [blockReconMass_eq, hS]
  have hpos0 : 0 < m 0 := quadForm_blockForm_zero_fieldFactor_pos p e x hreg g hg
  have hSpos : 0 < ∑ j, m j :=
    lt_of_lt_of_le hpos0 (Finset.single_le_sum (fun j _ => hm0 j) (Finset.mem_univ 0))
  have hmj : ∀ j, j ≠ 0 → m j = p.c * lpm (leadBlockPos p j) := fun j hj =>
    blockForm_fieldFactor_eq p e x hreg g j hj
  have hc : 0 < p.c := by have := p.b_lt_half; unfold Parameters.c; linarith
  have hΦ : ∀ μ ν : MassProfile, |Φ μ - Φ ν| ≤ 2 * ‖Φ‖ := fun μ ν => by
    refine (abs_sub _ _).trans ?_
    have h1 := Φ.norm_coe_le_norm μ
    have h2 := Φ.norm_coe_le_norm ν
    rw [Real.norm_eq_abs] at h1 h2
    linarith
  have hfrac0 : 0 ≤ m 0 / ∑ j, m j := div_nonneg (hm0 0) hSpos.le
  -- the per-rotation bound
  have hrot : ∀ s : ZMod p.n,
      |Φ (massProfileRotation (physicalProfileGrid p s)
          (massVectorProfile p (blockReconMass p 0 ω e v))) -
        Φ (leadProfile p.b e p.n p.W x.1 h s.val)| ≤
        ε + 2 * max C₀ ‖Φ‖ * (m 0 / ∑ j, m j) := by
    intro s
    rcases (Finset.single_le_sum (fun j _ => hm0 j) (Finset.mem_univ (0 : ZMod p.n))).lt_or_eq
      with hlt | heq
    · -- positive lead mass: the deletion estimate
      have htot : ∑ x', lpm x' = (∑ j, m j - m 0) / p.c := by
        rw [sum_leadPositions p lpm, ← sum_ite_zero_eq, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = 0
        · simp [hj]
        · simp only [hj, ↓reduceIte]
          rw [hmj j hj]; field_simp
      have htotpos : 0 < ∑ x', lpm x' := by
        rw [htot]; exact div_pos (by linarith) hc
      have hν' : (leadProfile p.b e p.n p.W x.1 h s.val : Measure Torus) =
          ∑ j, ENNReal.ofReal (deletedMass m 0 j) •
            Measure.dirac (physicalProfileGrid p (j + s)) := by
        rw [coe_leadProfile_of p.b e p.n p.W x.1 h s.val htotpos, sum_leadPositions p]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = 0
        · simp [hj, deletedMass]
        · simp only [hj, ↓reduceIte]
          have hval : (((leadRingBlock (p.n - 3) (leadBlockPos p j) + s.val) % p.n : ℕ) : ℝ) =
              ((j + s).val : ℝ) := by
            rw [leadRingBlock_leadBlockPos p j hj, ZMod.val_add]
          rw [hval]
          congr 2
          change lpm (leadBlockPos p j) / ∑ x', lpm x' = deletedMass m 0 j
          rw [htot, deletedMass]
          simp only [hj, ↓reduceIte]
          rw [hmj j hj]
          have : ∑ j', m j' - m 0 ≠ 0 := by linarith
          field_simp
      have hν : (massProfileRotation (physicalProfileGrid p s)
          (massVectorProfile p (blockReconMass p 0 ω e v)) : Measure Torus) =
          ∑ j, ENNReal.ofReal (m j / ∑ j', m j') •
            Measure.dirac (physicalProfileGrid p (j + s)) := by
        rw [coe_rotation_massVectorProfile p _ (fun j => by
            rw [hrecon]; exact div_nonneg (hm0 j) hSpos.le)
          (by simp_rw [hrecon]; rw [← Finset.sum_div, div_self hSpos.ne']) s]
        simp_rw [hrecon]
      have hd := hdel m hm0 0 hlt (fun j => physicalProfileGrid p (j + s)) _ _ hν hν'
      rw [abs_sub_comm]
      have : C₀ * (2 * (m 0 / ∑ j, m j)) ≤ 2 * max C₀ ‖Φ‖ * (m 0 / ∑ j, m j) := by
        have := le_max_left C₀ ‖Φ‖
        nlinarith
      linarith
    · -- all the mass on block `0`
      have h1 : m 0 / ∑ j, m j = 1 := by rw [← heq, div_self hpos0.ne']
      rw [h1, mul_one]
      have := hΦ (massProfileRotation (physicalProfileGrid p s)
          (massVectorProfile p (blockReconMass p 0 ω e v)))
        (leadProfile p.b e p.n p.W x.1 h s.val)
      have := le_max_right C₀ ‖Φ‖
      linarith
  -- average over the rotations
  unfold leadReconObservable leadProfileRotationAverage
  rw [← sum_zmod_eq_sum_range p (fun J => Φ (leadProfile p.b e p.n p.W x.1 h J)), ← mul_sub,
    ← Finset.sum_sub_distrib]
  have hn : (0 : ℝ) < p.n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.n)
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn), hrecon 0]
  calc (p.n : ℝ)⁻¹ * |∑ s : ZMod p.n, (Φ (massProfileRotation (physicalProfileGrid p s)
          (massVectorProfile p (blockReconMass p 0 ω e v))) -
        Φ (leadProfile p.b e p.n p.W x.1 h s.val))|
      ≤ (p.n : ℝ)⁻¹ * ∑ _s : ZMod p.n, (ε + 2 * max C₀ ‖Φ‖ * (m 0 / ∑ j, m j)) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => hrot s)
    _ = ε + 2 * max C₀ ‖Φ‖ * (m 0 / ∑ j, m j) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
        field_simp

end Pointwise

end LeadGaussian

end BlockBand.Endpoints.Normalization
