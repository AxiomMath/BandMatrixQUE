module

public import BlockBand.Density.ResolventComparison
public import BlockBand.Density.CouplingEntries

/-!
# Coupling of the physical ring with a short ring on a retained segment

Around a site retain `m` consecutive blocks and close this segment with an independent Gaussian
bond, to obtain a matrix with exactly the short-ring law. Parameters: any admissible `p`
(`n` blocks), `4 ≤ m < n`; the short ring `shortParameters p m` has `m` blocks and the same `W, b`.

* `segmentEmbedding`: block `k ∈ ZMod m` of the short ring is block `k.val ∈ ZMod n` of `p`
  (the retained segment is blocks `0, …, m-1`); it preserves the row-major index;
* `closingBond`: the entries between short-ring blocks `0` and `m-1` (the closing bond);
* `coupledShortMatrix (H, K')`: the short-ring matrix equal to `H` on the segment except on the
  closing bond, where it reads the independent `K'`;
* `coupledLaw model model'`: the product law `P_p ⊗ P_q` of `(H, K')` (enlarged space);
* `coupledShort_isPhysical`: the pushforward of `coupledLaw` by `coupledShortMatrix` has exactly
  the physical short-ring law (`IsPhysicalGaussianRingLaw (shortParameters p m)`, joint
  characteristic function), so `coupledShortModel` is a `GaussianRingModel` of the short ring;
  the first marginal of `coupledLaw` is the original law `model.law`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory

/-- The short ring: `m` blocks, the same width `W` and bond `b` as `p`. -/
def shortParameters (p : Parameters) (m : ℕ) (hm : 4 ≤ m) : Parameters :=
  ⟨m, p.W, p.b, hm, p.W_pos, p.b_pos, p.b_lt_half⟩

/-- Sums over the strict upper triangle of an index order transported along an injection, for
a summand vanishing off the image. -/
theorem sum_upper_transport {α β : Type} [Fintype α] [Fintype β] {ι : β → α}
    (hι : Function.Injective ι) (sα : α → ℕ) (sβ : β → ℕ) (hs : ∀ b, sα (ι b) = sβ b)
    (T : α → α → ℝ) (hT : ∀ x y, (¬∃ r : β × β, Prod.map ι ι r = (x, y)) → T x y = 0) :
    ∑ x, ∑ y with sα x < sα y, T x y = ∑ a, ∑ b with sβ a < sβ b, T (ι a) (ι b) := by
  simp only [Finset.sum_filter]
  rw [← Fintype.sum_prod_type' (fun x y => if sα x < sα y then T x y else 0),
    ← Fintype.sum_prod_type' (fun a b => if sβ a < sβ b then T (ι a) (ι b) else 0)]
  symm
  refine Fintype.sum_of_injective (Prod.map ι ι) (hι.prodMap hι) _ _ ?_ ?_
  · intro r hr
    have : ¬∃ r' : β × β, Prod.map ι ι r' = (r.1, r.2) := by
      rintro ⟨r', hr'⟩
      exact hr ⟨r', hr'⟩
    simp [hT r.1 r.2 this]
  · intro r
    simp [hs]

section Embedding

variable (p : Parameters) {m : ℕ} (hm : 4 ≤ m)

/-- The retained segment: short-ring block `k` is block `k.val` of the ring `p`. -/
def segmentEmbedding (u : (shortParameters p m hm).Site) : p.Site :=
  ((u.1.val : ZMod p.n), u.2)

/-- The closing bond of the short ring: entries between blocks `0` and `m - 1`. -/
def closingBond (u v : (shortParameters p m hm).Site) : Prop :=
  (u.1.val = 0 ∧ v.1.val = m - 1) ∨ (u.1.val = m - 1 ∧ v.1.val = 0)

instance (u v : (shortParameters p m hm).Site) : Decidable (closingBond p hm u v) := by
  unfold closingBond; infer_instance

variable {p hm}

theorem val_segmentEmbedding (hmn : m < p.n) (u : (shortParameters p m hm).Site) :
    (segmentEmbedding p hm u).1.val = u.1.val := by
  have hu : u.1.val < m := ZMod.val_lt (n := (shortParameters p m hm).n) u.1
  simp only [segmentEmbedding, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (hu.trans hmn)

theorem segmentEmbedding_injective (hmn : m < p.n) :
    Function.Injective (segmentEmbedding p hm) := by
  intro u v h
  have h1 : u.1.val = v.1.val := by
    rw [← val_segmentEmbedding hmn u, ← val_segmentEmbedding hmn v, h]
  have h2 : u.2 = v.2 := by
    have := congrArg Prod.snd h
    exact this
  exact Prod.ext (ZMod.val_injective _ h1) h2

theorem siteIndex_segmentEmbedding (hmn : m < p.n) (u : (shortParameters p m hm).Site) :
    p.siteIndex (segmentEmbedding p hm u) = (shortParameters p m hm).siteIndex u := by
  simp only [Parameters.siteIndex, val_segmentEmbedding hmn u]
  rfl

theorem closingBond_symm (u v : (shortParameters p m hm).Site) :
    closingBond p hm v u ↔ closingBond p hm u v := by
  unfold closingBond; tauto

theorem not_closingBond_self (u : (shortParameters p m hm).Site) : ¬closingBond p hm u u := by
  unfold closingBond; omega

/-- `X = Y + 1` in `ZMod k` through values. -/
theorem zmod_eq_add_one_iff {k : ℕ} [NeZero k] (hk : 1 < k) (X Y : ZMod k) :
    X = Y + 1 ↔ X.val = (Y.val + 1) % k := by
  constructor
  · intro h
    rw [h, ZMod.val_add, ZMod.val_one'' (by omega)]
  · intro h
    apply ZMod.val_injective
    rw [h, ZMod.val_add, ZMod.val_one'' (by omega)]

theorem zmod_eq_sub_one_iff {k : ℕ} [NeZero k] (hk : 1 < k) (X Y : ZMod k) :
    X = Y - 1 ↔ Y.val = (X.val + 1) % k := by
  rw [← zmod_eq_add_one_iff hk, eq_sub_iff_add_eq, eq_comm]

theorem succ_mod_eq {t k : ℕ} (ht : t < k) : (t + 1) % k = if t + 1 = k then 0 else t + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Off the closing bond the segment carries the short-ring variance profile. -/
theorem entryVariance_segmentEmbedding (hmn : m < p.n) (a b : (shortParameters p m hm).Site)
    (h : ¬closingBond p hm a b) :
    p.entryVariance (segmentEmbedding p hm a) (segmentEmbedding p hm b) =
      (shortParameters p m hm).entryVariance a b := by
  have ha : a.1.val < m := ZMod.val_lt (n := (shortParameters p m hm).n) a.1
  have hb : b.1.val < m := ZMod.val_lt (n := (shortParameters p m hm).n) b.1
  have hn1 : 1 < p.n := by omega
  have hm1 : 1 < (shortParameters p m hm).n := by change 1 < m; omega
  have hva := val_segmentEmbedding hmn a
  have hvb := val_segmentEmbedding hmn b
  have h1 : (segmentEmbedding p hm b).1 = (segmentEmbedding p hm a).1 ↔ b.1 = a.1 := by
    rw [← (ZMod.val_injective p.n).eq_iff, hva, hvb, (ZMod.val_injective _).eq_iff]
  have h2 : ((segmentEmbedding p hm b).1 = (segmentEmbedding p hm a).1 + 1 ∨
      (segmentEmbedding p hm b).1 = (segmentEmbedding p hm a).1 - 1) ↔
      (b.1 = a.1 + 1 ∨ b.1 = a.1 - 1) := by
    rw [zmod_eq_add_one_iff hn1, zmod_eq_sub_one_iff hn1, zmod_eq_add_one_iff hm1,
      zmod_eq_sub_one_iff hm1, hva, hvb, succ_mod_eq (ha.trans hmn), succ_mod_eq (hb.trans hmn),
      succ_mod_eq (k := (shortParameters p m hm).n) ha,
      succ_mod_eq (k := (shortParameters p m hm).n) hb]
    unfold closingBond at h
    have hq : (shortParameters p m hm).n = m := rfl
    split_ifs <;> omega
  simp only [Parameters.entryVariance, h1, h2]
  rfl

end Embedding

section Law

variable {p : Parameters} {m : ℕ} {hm : 4 ≤ m}

/-- The short-ring matrix of the coupling: `H` on the segment, the independent `K'` on the
closing bond. -/
def coupledShortMatrix (ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix) :
    (shortParameters p m hm).SiteMatrix := fun u v =>
  if closingBond p hm u v then ω.2 u v else ω.1 (segmentEmbedding p hm u) (segmentEmbedding p hm v)

theorem measurable_coupledShortMatrix :
    Measurable (coupledShortMatrix (p := p) (hm := hm)) := by
  apply measurable_pi_iff.mpr
  intro u
  apply measurable_pi_iff.mpr
  intro v
  unfold coupledShortMatrix
  split_ifs
  · exact (measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_snd)
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)

theorem coupledShortMatrix_isHermitian {ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix}
    (h1 : ω.1.IsHermitian) (h2 : ω.2.IsHermitian) : (coupledShortMatrix ω).IsHermitian := by
  ext u v
  simp only [Matrix.conjTranspose_apply, coupledShortMatrix, closingBond_symm u v]
  split_ifs
  · exact congrFun (congrFun h2 u) v
  · exact congrFun (congrFun h1 _) _

/-- Diagonal coefficients pushed to the ring. -/
def pushDiag (d : (shortParameters p m hm).Site → ℝ) : p.Site → ℝ :=
  Function.extend (segmentEmbedding p hm) d 0

/-- Off-closing-bond coefficients pushed to the ring. -/
def pushOff (u : (shortParameters p m hm).Site → (shortParameters p m hm).Site → ℝ) :
    p.Site → p.Site → ℝ := fun x y =>
  Function.extend (Prod.map (segmentEmbedding p hm) (segmentEmbedding p hm))
    (fun r => if closingBond p hm r.1 r.2 then 0 else u r.1 r.2) 0 (x, y)

/-- Closing-bond coefficients. -/
def closingPart (u : (shortParameters p m hm).Site → (shortParameters p m hm).Site → ℝ) :
    (shortParameters p m hm).Site → (shortParameters p m hm).Site → ℝ := fun a b =>
  if closingBond p hm a b then u a b else 0

theorem pushOff_apply (hmn : m < p.n)
    (u : (shortParameters p m hm).Site → (shortParameters p m hm).Site → ℝ)
    (a b : (shortParameters p m hm).Site) :
    pushOff u (segmentEmbedding p hm a) (segmentEmbedding p hm b) =
      if closingBond p hm a b then 0 else u a b :=
  ((segmentEmbedding_injective hmn).prodMap (segmentEmbedding_injective hmn)).extend_apply
    (fun r => if closingBond p hm r.1 r.2 then 0 else u r.1 r.2) 0 (a, b)

theorem pushOff_of_not_mem
    (u : (shortParameters p m hm).Site → (shortParameters p m hm).Site → ℝ) {x y : p.Site}
    (h : ¬∃ r : (shortParameters p m hm).Site × (shortParameters p m hm).Site,
      Prod.map (segmentEmbedding p hm) (segmentEmbedding p hm) r = (x, y)) :
    pushOff u x y = 0 := by
  unfold pushOff
  rw [Function.extend_apply' _ _ _ h]
  rfl

theorem sum_pushDiag (hmn : m < p.n) (d : (shortParameters p m hm).Site → ℝ)
    (F : p.Site → ℝ → ℝ) (hF : ∀ x, F x 0 = 0) :
    ∑ x, F x (pushDiag d x) = ∑ a, F (segmentEmbedding p hm a) (d a) := by
  symm
  refine Fintype.sum_of_injective _ (segmentEmbedding_injective hmn) _ _ ?_ ?_
  · intro x hx
    have : pushDiag d x = 0 := by
      unfold pushDiag
      rw [Function.extend_apply' _ _ _ (by simpa [Set.mem_range] using hx)]
      rfl
    rw [this, hF]
  · intro a
    unfold pushDiag
    rw [(segmentEmbedding_injective hmn).extend_apply]

/-- The joint characteristic pairing splits into a ring part and a closing-bond part. -/
theorem coordinatePairing_coupled (hmn : m < p.n) (d : (shortParameters p m hm).Site → ℝ)
    (u v : (shortParameters p m hm).Site → (shortParameters p m hm).Site → ℝ)
    (ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix) :
    (shortParameters p m hm).coordinatePairing d u v (coupledShortMatrix ω) =
      p.coordinatePairing (pushDiag d) (pushOff u) (pushOff v) ω.1 +
        (shortParameters p m hm).coordinatePairing 0 (closingPart u) (closingPart v) ω.2 := by
  have hι := segmentEmbedding_injective (hm := hm) hmn
  unfold Parameters.coordinatePairing
  have hdiag : ∑ x, pushDiag d x * (ω.1 x x).re =
      ∑ a, d a * (coupledShortMatrix ω a a).re := by
    rw [sum_pushDiag hmn d (fun x t => t * (ω.1 x x).re) (fun x => zero_mul _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [coupledShortMatrix, not_closingBond_self]
  have hoff := sum_upper_transport hι p.siteIndex (shortParameters p m hm).siteIndex
    (siteIndex_segmentEmbedding hmn)
    (fun x y => pushOff u x y * (ω.1 x y).re + pushOff v x y * (ω.1 x y).im)
    (fun x y h => by simp [pushOff_of_not_mem u h, pushOff_of_not_mem v h])
  simp only [pushOff_apply hmn] at hoff
  have hinner : ∀ a b, u a b * (coupledShortMatrix ω a b).re + v a b * (coupledShortMatrix ω a b).im =
      ((if closingBond p hm a b then 0 else u a b) *
          (ω.1 (segmentEmbedding p hm a) (segmentEmbedding p hm b)).re +
        (if closingBond p hm a b then 0 else v a b) *
          (ω.1 (segmentEmbedding p hm a) (segmentEmbedding p hm b)).im) +
      (closingPart u a b * (ω.2 a b).re + closingPart v a b * (ω.2 a b).im) := by
    intro a b
    simp only [coupledShortMatrix, closingPart]
    split_ifs <;> ring
  rw [hdiag, hoff]
  simp only [hinner, Finset.sum_add_distrib, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add]
  ring

/-- The joint characteristic variance splits in the same way (off the closing bond the
segment carries the short-ring variances). -/
theorem coordinateVariance_coupled (hmn : m < p.n) (d : (shortParameters p m hm).Site → ℝ)
    (u v : (shortParameters p m hm).Site → (shortParameters p m hm).Site → ℝ) :
    (shortParameters p m hm).coordinateVariance d u v =
      p.coordinateVariance (pushDiag d) (pushOff u) (pushOff v) +
        (shortParameters p m hm).coordinateVariance 0 (closingPart u) (closingPart v) := by
  have hι := segmentEmbedding_injective (hm := hm) hmn
  unfold Parameters.coordinateVariance
  have hdiag : ∑ x, p.entryVariance x x * pushDiag d x ^ 2 =
      ∑ a, (shortParameters p m hm).entryVariance a a * d a ^ 2 := by
    rw [sum_pushDiag hmn d (fun x t => p.entryVariance x x * t ^ 2) (fun x => by simp)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [entryVariance_segmentEmbedding hmn a a (not_closingBond_self a)]
  have hoff := sum_upper_transport hι p.siteIndex (shortParameters p m hm).siteIndex
    (siteIndex_segmentEmbedding hmn)
    (fun x y => p.entryVariance x y / 2 * (pushOff u x y ^ 2 + pushOff v x y ^ 2))
    (fun x y h => by simp [pushOff_of_not_mem u h, pushOff_of_not_mem v h])
  simp only [pushOff_apply hmn] at hoff
  have hinner : ∀ a b, (shortParameters p m hm).entryVariance a b / 2 * (u a b ^ 2 + v a b ^ 2) =
      p.entryVariance (segmentEmbedding p hm a) (segmentEmbedding p hm b) / 2 *
          ((if closingBond p hm a b then 0 else u a b) ^ 2 +
            (if closingBond p hm a b then 0 else v a b) ^ 2) +
        (shortParameters p m hm).entryVariance a b / 2 *
          (closingPart u a b ^ 2 + closingPart v a b ^ 2) := by
    intro a b
    simp only [closingPart]
    split_ifs with hc
    · ring
    · rw [entryVariance_segmentEmbedding hmn a b hc]; ring
  rw [hdiag, hoff]
  simp only [hinner, Finset.sum_add_distrib, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, zero_add]
  ring

theorem continuous_coordinatePairing (q : Parameters) (d : q.Site → ℝ) (u v : q.Site → q.Site → ℝ) :
    Continuous (q.coordinatePairing d u v) := by
  unfold Parameters.coordinatePairing
  fun_prop

/-- The law of `(H, K')` on the enlarged space: the product of the ring law and an independent
short-ring law. -/
def coupledLaw (model : p.GaussianRingModel) (model' : (shortParameters p m hm).GaussianRingModel) :
    Measure (p.SiteMatrix × (shortParameters p m hm).SiteMatrix) :=
  (model.law : Measure p.SiteMatrix).prod (model'.law : Measure (shortParameters p m hm).SiteMatrix)

instance (model : p.GaussianRingModel) (model' : (shortParameters p m hm).GaussianRingModel) :
    IsProbabilityMeasure (coupledLaw model model') := by
  unfold coupledLaw; infer_instance

theorem ae_fst_isHermitian (model : p.GaussianRingModel)
    (model' : (shortParameters p m hm).GaussianRingModel) :
    ∀ᵐ ω ∂(coupledLaw model model'), ω.1.IsHermitian := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  unfold coupledLaw
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact model.isPhysical.1

theorem ae_snd_isHermitian (model : p.GaussianRingModel)
    (model' : (shortParameters p m hm).GaussianRingModel) :
    ∀ᵐ ω ∂(coupledLaw model model'), ω.2.IsHermitian := by
  apply ae_of_ae_map measurable_snd.aemeasurable
  unfold coupledLaw
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  exact model'.isPhysical.1

/-- The first marginal of the coupling is the ring law. -/
theorem integral_coupledLaw_fst (model : p.GaussianRingModel)
    (model' : (shortParameters p m hm).GaussianRingModel) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : p.SiteMatrix → E) :
    ∫ ω, f ω.1 ∂(coupledLaw model model') = ∫ H, f H ∂(model.law : Measure p.SiteMatrix) := by
  unfold coupledLaw
  rw [integral_fun_fst, probReal_univ, one_smul]

/-- The second marginal of the coupling is the independent short-ring law. -/
theorem integral_coupledLaw_snd (model : p.GaussianRingModel)
    (model' : (shortParameters p m hm).GaussianRingModel) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (shortParameters p m hm).SiteMatrix → E) :
    ∫ ω, f ω.2 ∂(coupledLaw model model') =
      ∫ K, f K ∂(model'.law : Measure (shortParameters p m hm).SiteMatrix) := by
  unfold coupledLaw
  rw [integral_fun_snd, probReal_univ, one_smul]

/-- **The coupled short-ring matrix has exactly the physical short-ring law.** -/
theorem coupledShort_isPhysical (hmn : m < p.n) (model : p.GaussianRingModel)
    (model' : (shortParameters p m hm).GaussianRingModel) :
    (shortParameters p m hm).IsPhysicalGaussianRingLaw
      ⟨Measure.map coupledShortMatrix (coupledLaw model model'),
        (Measure.isProbabilityMeasure_map_iff measurable_coupledShortMatrix.aemeasurable).mpr inferInstance⟩ := by
  constructor
  · change ∀ᵐ K ∂(Measure.map coupledShortMatrix (coupledLaw model model')), K.IsHermitian
    have hset : MeasurableSet {K : (shortParameters p m hm).SiteMatrix | K.IsHermitian} :=
      (isClosed_eq (by fun_prop : Continuous fun H : (shortParameters p m hm).SiteMatrix =>
        H.conjTranspose) continuous_id).measurableSet
    rw [ae_map_iff measurable_coupledShortMatrix.aemeasurable hset]
    filter_upwards [ae_fst_isHermitian model model', ae_snd_isHermitian model model'] with ω h1 h2
    exact coupledShortMatrix_isHermitian h1 h2
  · intro d u v
    change ∫ K, Complex.exp (Complex.I * ((shortParameters p m hm).coordinatePairing d u v K : ℂ))
      ∂(Measure.map coupledShortMatrix (coupledLaw model model')) = _
    have hc : Continuous fun K : (shortParameters p m hm).SiteMatrix =>
        Complex.exp (Complex.I * ((shortParameters p m hm).coordinatePairing d u v K : ℂ)) := by
      have := continuous_coordinatePairing (shortParameters p m hm) d u v
      fun_prop
    rw [integral_map measurable_coupledShortMatrix.aemeasurable hc.aestronglyMeasurable]
    simp_rw [coordinatePairing_coupled hmn d u v, Complex.ofReal_add, mul_add, Complex.exp_add]
    unfold coupledLaw
    rw [integral_prod_mul (fun H : p.SiteMatrix =>
        Complex.exp (Complex.I * (p.coordinatePairing (pushDiag d) (pushOff u) (pushOff v) H : ℂ)))
      (fun K : (shortParameters p m hm).SiteMatrix => Complex.exp (Complex.I *
        ((shortParameters p m hm).coordinatePairing 0 (closingPart u) (closingPart v) K : ℂ))),
      model.isPhysical.2, model'.isPhysical.2, ← Complex.exp_add,
      coordinateVariance_coupled hmn d u v]
    congr 1
    push_cast
    ring

/-- The coupled short ring as a `GaussianRingModel` of `shortParameters p m`. -/
def coupledShortModel (hmn : m < p.n) (model : p.GaussianRingModel)
    (model' : (shortParameters p m hm).GaussianRingModel) :
    (shortParameters p m hm).GaussianRingModel where
  law := ⟨Measure.map coupledShortMatrix (coupledLaw model model'),
    (Measure.isProbabilityMeasure_map_iff measurable_coupledShortMatrix.aemeasurable).mpr inferInstance⟩
  isPhysical := coupledShort_isPhysical hmn model model'

end Law

end BlockBand.Density
