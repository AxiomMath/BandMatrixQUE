module

public import BlockBand.Transmission.FractionalBulk.Concave
public import BlockBand.Transmission.Generator.StepExact

/-!
# One fresh layer: the measurable step functional and the per-sample bound

* `stepFrac p b E X y = clip_{[0,W]} fracInt p T(X₊(y))`: jointly measurable
  (`measurable_stepFrac`), `0 ≤ stepFrac ≤ W`;
* `lowFrac p T = Σ_{t_i ≤ 1/2} t_i^p` (`lowFrac_eq_sum`), and
  `lowFrac p T ≥ Tr T^p - 2 Tr T` for `0 ⪯ T ⪯ I` (`lowFrac_ge`: at most `2g` eigenvalues exceed
  `1/2`);
* `isOrthonormalEigenbasis_ts`: Mathlib's eigenbasis is an `IsOrthonormalEigenbasis`;
* `ae_stepFrac_eq`: a.s. `stepFrac = Tr (ΔZΔ)^p`, `Z = V*UV`, `Δ = diag(√t)` (by
  `sand_freshU_eq`: the new `T₊ = L*TL` and `ΔZΔ = GG*` with `G*G = T₊`);
* `sample_bound`: the deterministic gap `fracTrace_sand_le` at `Z = V*UV`, `N = max(1, ‖L‖²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.Generator
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Clip to `[0, W]`. -/
def clipW (W : ℕ) (x : ℝ) : ℝ := max 0 (min x W)

theorem clipW_nonneg (W : ℕ) (x : ℝ) : 0 ≤ clipW W x := le_max_left _ _

theorem clipW_le (W : ℕ) (x : ℝ) : clipW W x ≤ W :=
  max_le (Nat.cast_nonneg _) (min_le_right _ _)

theorem clipW_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ W) : clipW W x = x := by
  rw [clipW, min_eq_left h1, max_eq_right h0]

theorem continuous_clipW (W : ℕ) : Continuous (clipW W) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The measurable one-step functional `clip(Tr T(X₊)^p)`. -/
def stepFrac (p b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : LayerSample W .oneBlockOnePort) : ℝ :=
  clipW W (fracInt p (passiveTransmission b E (freshSchur E X y)))

theorem measurable_passiveTransmission (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveTransmission b E X :=
  (continuous_const_smul _).measurable.comp (mu_measurable_passiveQ b E)

theorem measurable_stepFrac (p b E : ℝ) :
    Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      stepFrac p b E q.1 q.2 :=
  (continuous_clipW W).measurable.comp ((measurable_fracInt p).comp
    ((measurable_passiveTransmission b E).comp (measurable_freshSchur_prod E)))

theorem stepFrac_nonneg (p b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y) :
    0 ≤ stepFrac p b E X y := clipW_nonneg _ _

theorem stepFrac_le (p b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y) :
    stepFrac p b E X y ≤ W := clipW_le _ _

/-- `Σ_{t_i ≤ 1/2} t_i^p`. -/
def lowFrac {n : Type*} [Fintype n] [DecidableEq n] (p : ℝ) (T : Matrix n n ℂ) : ℝ :=
  (T.charpoly.roots.map fun z => if z.re ≤ 1 / 2 then (max z.re 0) ^ p else 0).sum

theorem lowFrac_eq_sum {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (p : ℝ) :
    lowFrac p T = ∑ i, if ts_lam hT i ≤ 1 / 2 then ts_lam hT i ^ p else 0 := by
  rw [lowFrac, hT.1.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [max_eq_left (hT.eigenvalues_nonneg i), ts_lam]

theorem fracTrace_eq_sum_ts {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (p : ℝ) :
    fracTrace p T = ∑ i, ts_lam hT i ^ p :=
  fracTrace_eq_sum_eigenvalues_psd hT p

theorem lowFrac_nonneg (p : ℝ) {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) :
    0 ≤ lowFrac p T := by
  rw [lowFrac_eq_sum hT]
  exact Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact Real.rpow_nonneg (ts_lam_nonneg hT i) _
    · exact le_rfl

/-- **`Σ_{t_i ≤ 1/2} t_i^p ≥ Tr T^p - 2 Tr T`** for `0 ⪯ T ⪯ I`, `p > 0`. -/
theorem lowFrac_ge {p : ℝ} (hp0 : 0 < p) {T : Matrix (Fin W) (Fin W) ℂ} (h0 : T.PosSemidef)
    (h1 : (1 - T).PosSemidef) : fracTrace p T - 2 * conductanceOf T ≤ lowFrac p T := by
  rw [lowFrac_eq_sum h0, fracTrace_eq_sum_ts h0, conductanceOf, ← ts_sum_lam h0, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hl0 := ts_lam_nonneg h0 i
  have hl1 := ts_lam_le_one h0 h1 i
  have hp1 : ts_lam h0 i ^ p ≤ 1 := Real.rpow_le_one hl0 hl1 hp0.le
  split_ifs with h
  · linarith
  · push Not at h
    have : 0 ≤ ts_lam h0 i ^ p := Real.rpow_nonneg hl0 _
    linarith

theorem isOrthonormalEigenbasis_ts {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) :
    IsOrthonormalEigenbasis T (ts_vec hT) (ts_lam hT) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have h := (orthonormal_iff_ite.mp hT.isHermitian.eigenvectorBasis.orthonormal) i j
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  · have := hT.isHermitian.mulVec_eigenvectorBasis i
    rw [ts_vec, this, ts_lam]
    rw [Complex.coe_smul]

/-- `Z = V*UV`. -/
abbrev eigU {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (U : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  star (ts_U hT) * U * ts_U hT

theorem eigU_apply {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef)
    (U : Matrix (Fin W) (Fin W) ℂ) (i j : Fin W) :
    eigU hT U i j = bilinear (ts_vec hT i) U (ts_vec hT j) := (ts_ent_eq hT U i j).symm

/-- **A.s. identification** `stepFrac = Tr (ΔZΔ)^p`. -/
theorem ae_stepFrac_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ} (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) :
    ∀ᵐ y ∂freshLaw W b, stepFrac p b E X y =
      fracTrace p (sqDiag (ts_lam hT) * eigU hT (freshU b E X y) * sqDiag (ts_lam hT)) := by
  filter_upwards [ae_transmission_fresh hb0 hb hW h1 h2 hY] with y hy
  have hTn : (passiveTransmission b E (freshSchur E X y)).PosSemidef := by
    rw [hy]; exact hT.conjTranspose_mul_mul_same _
  have hTn1 := one_sub_passiveTransmission_posSemidef b E (freshSchur E X y)
  have hfr := fracTrace_eq_fracInt hTn hp0 hp1
  have hmem0 := fracTrace_nonneg' p (passiveTransmission b E (freshSchur E X y))
  have hmem1 := fracTrace_le_card hTn hTn1 hp0
  rw [Fintype.card_fin] at hmem1
  rw [stepFrac, ← hfr, clipW_of_mem hmem0 hmem1]
  obtain ⟨e1, e2⟩ := sand_freshU_eq hT (freshL b E X y)
  have hs : sqDiag (ts_lam hT) * eigU hT (freshU b E X y) * sqDiag (ts_lam hT) =
      sand hT (freshL b E X y * (freshL b E X y)ᴴ) := rfl
  rw [hs, e1, hy, ← e2]
  exact fracTrace_congr' (Matrix.charpoly_mul_comm _ _)

theorem eigU_posSemidef {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef)
    (L : Matrix (Fin W) (Fin W) ℂ) : (eigU hT (L * Lᴴ)).PosSemidef := by
  have := (Matrix.posSemidef_self_mul_conjTranspose L).conjTranspose_mul_mul_same (ts_U hT)
  rwa [← Matrix.star_eq_conjTranspose] at this

theorem eigU_form_le {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef)
    (L : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    (star v ⬝ᵥ (eigU hT (L * Lᴴ) *ᵥ v)).re ≤ max 1 (‖L‖ ^ 2) * ∑ k, ‖v k‖ ^ 2 := by
  have hb := norm_bilinear_le v (eigU hT (L * Lᴴ)) v
  have hV : ‖ts_U hT‖ ≤ 1 := norm_unitary_le (ts_U_star_mul hT)
  have hV' : ‖star (ts_U hT)‖ ≤ 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]; exact hV
  have hn : ‖eigU hT (L * Lᴴ)‖ ≤ ‖L‖ ^ 2 := by
    calc ‖eigU hT (L * Lᴴ)‖ ≤ ‖star (ts_U hT)‖ * ‖L * Lᴴ‖ * ‖ts_U hT‖ :=
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ ≤ 1 * ‖L * Lᴴ‖ * 1 := by gcongr
      _ = ‖L‖ ^ 2 := by
          rw [one_mul, mul_one, sq]
          have := Matrix.l2_opNorm_conjTranspose_mul_self Lᴴ
          rwa [conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at this
  have hv2 : vecNorm v * vecNorm v = ∑ k, ‖v k‖ ^ 2 := by
    rw [← sq, vecNorm, Real.sq_sqrt (by positivity)]
  calc (star v ⬝ᵥ (eigU hT (L * Lᴴ) *ᵥ v)).re ≤ ‖bilinear v (eigU hT (L * Lᴴ)) v‖ :=
        Complex.re_le_norm _
    _ ≤ vecNorm v * ‖eigU hT (L * Lᴴ)‖ * vecNorm v := hb
    _ = ‖eigU hT (L * Lᴴ)‖ * (vecNorm v * vecNorm v) := by ring
    _ ≤ max 1 (‖L‖ ^ 2) * ∑ k, ‖v k‖ ^ 2 := by
        rw [hv2]
        exact mul_le_mul_of_nonneg_right (hn.trans (le_max_right _ _)) (by positivity)

/-- **The per-sample bound** at `Z = V*UV`, `N = max(1, ‖L‖²)`. -/
theorem sample_bound {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {T : Matrix (Fin W) (Fin W) ℂ}
    (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef) (L : Matrix (Fin W) (Fin W) ℂ) :
    fracTrace p (sqDiag (ts_lam hT) * eigU hT (L * Lᴴ) * sqDiag (ts_lam hT)) ≤
      ∑ i, ts_lam hT i ^ p + cP p * jP p * ∑ i, ts_lam hT i ^ p * ((eigU hT (L * Lᴴ) i i).re - 1) -
      cP p / (27 * max 1 (‖L‖ ^ 2)) * ∑ i, ∑ j, (if ts_lam hT i ≤ ts_lam hT j then
        ts_lam hT i ^ p * ts_lam hT j ^ p *
          ‖eigU hT (L * Lᴴ) j i - (1 : Matrix (Fin W) (Fin W) ℂ) j i‖ ^ 2 else 0) :=
  fracTrace_sand_le hp0 hp1 (ts_lam_nonneg hT) (ts_lam_le_one hT hT1) (eigU_posSemidef hT L)
    (le_max_left _ _) (eigU_form_le hT L)

end BlockBand.Transmission.FractionalBulk
